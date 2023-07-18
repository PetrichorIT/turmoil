use crate::config::Config;
use crate::envelope::Protocol;
use crate::host::HostIdentifier;
use crate::ip::IpSubnets;
use crate::{config, Dns, Host, ToIpAddrs, Topology, TRACING_TARGET};

use indexmap::IndexMap;
use rand::RngCore;
use scoped_tls::scoped_thread_local;
use std::cell::RefCell;
use std::net::{IpAddr, SocketAddr};
use std::time::Duration;

/// Tracks all the state for the simulated world.
pub(crate) struct World {
    /// Tracks all individual hosts
    pub(crate) hosts: IndexMap<HostIdentifier, Host>,

    /// Tracks how each host is connected to each other.
    pub(crate) topology: Topology,

    /// Maps hostnames to ip addresses.
    pub(crate) dns: Dns,

    /// If set, this is the current host being executed.
    pub(crate) current: Option<HostIdentifier>,

    /// Random number generator used for all decisions. To make execution
    /// determinstic, reuse the same seed.
    pub(crate) rng: Box<dyn RngCore>,
}

scoped_thread_local!(static CURRENT: RefCell<World>);

impl World {
    /// Initialize a new world.
    pub(crate) fn new(link: config::Link, rng: Box<dyn RngCore>, subnets: IpSubnets) -> World {
        World {
            hosts: IndexMap::new(),
            topology: Topology::new(link),
            dns: Dns::new(subnets.addrs_iter()),
            current: None,
            rng,
        }
    }

    /// Run `f` on the world.
    pub(crate) fn current<R>(f: impl FnOnce(&mut World) -> R) -> R {
        CURRENT.with(|current| {
            let mut current = current.borrow_mut();
            f(&mut current)
        })
    }

    /// Run `f` if the world is set - otherwise no-op.
    ///
    /// Used in drop paths, where the simulation may be shutting
    /// down and we don't need to do anything.
    pub(crate) fn current_if_set(f: impl FnOnce(&mut World)) {
        if CURRENT.is_set() {
            Self::current(f);
        }
    }

    pub(crate) fn enter<R>(world: &RefCell<World>, f: impl FnOnce() -> R) -> R {
        CURRENT.set(world, f)
    }

    pub(crate) fn current_host_mut(&mut self) -> &mut Host {
        let addr = self.current.expect("current host missing");
        self.hosts.get_mut(&addr).expect("host missing")
    }

    pub(crate) fn lookup(&mut self, host: impl ToIpAddrs) -> Vec<IpAddr> {
        self.dns.lookup(host)
    }

    pub(crate) fn hold(&mut self, a: IpAddr, b: IpAddr) {
        self.topology.hold(a, b);
    }

    pub(crate) fn release(&mut self, a: IpAddr, b: IpAddr) {
        self.topology.release(a, b);
    }

    pub(crate) fn partition(&mut self, a: IpAddr, b: IpAddr) {
        self.topology.partition(a, b);
    }

    pub(crate) fn repair(&mut self, a: IpAddr, b: IpAddr) {
        self.topology.repair(a, b);
    }

    /// Register a new host with the simulation.
    pub(crate) fn register(&mut self, id: HostIdentifier, addr: impl ToIpAddrs, config: &Config) {
        let addrs = self.dns.register(addr);

        tracing::info!(target: TRACING_TARGET, hostname = ?self.dns.reverse(addrs[0]), %addrs, "New");

        // Register links between the new host and all existing hosts
        for existing in self.hosts.values() {
            for (&lhs, &rhs) in existing.addrs.iter().zip(addrs.iter()) {
                self.topology.register(lhs, rhs)
            }
        }

        // Initialize host state
        self.hosts.insert(
            id,
            Host::new(addrs, config.tcp_capacity, config.udp_capacity),
        );
    }

    /// Send `message` from `src` to `dst`. Delivery is asynchronous and not
    /// guaranteed.
    pub(crate) fn send_message(&mut self, src: SocketAddr, dst: SocketAddr, message: Protocol) {
        self.topology
            .enqueue_message(&mut self.rng, src, dst, message);
    }

    /// Tick the host at `addr` by `duration`.
    pub(crate) fn tick(&mut self, host: HostIdentifier, duration: Duration) {
        self.hosts
            .get_mut(&host)
            .expect("missing host")
            .tick(duration);
    }
}
