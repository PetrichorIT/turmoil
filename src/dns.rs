use indexmap::IndexMap;
#[cfg(feature = "regex")]
use regex::Regex;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};

use crate::ip::{HostAddrs, IpSubnetIter};

/// Each new host has an IP in the subnet defined by the
/// ip version of the simulation.
///
/// Ipv4 simulations use the subnet 192.168.0.0/16.
/// Ipv6 simulations use the link local subnet fe80:::/64
pub struct Dns {
    addrs: IpSubnetIter,
    names: IndexMap<String, HostAddrs>,
}

/// Converts or resolves to one or more [`IpAddr`] values.
pub trait ToIpAddrs: sealed::Sealed {
    #[doc(hidden)]
    fn to_ip_addrs(&self, dns: &Dns) -> Vec<IpAddr>;

    #[doc(hidden)]
    fn register(&self, dns: &mut Dns) -> HostAddrs;
}

/// A simulated version of `tokio::net::ToSocketAddrs`.
pub trait ToSocketAddrs: sealed::Sealed {
    #[doc(hidden)]
    fn to_socket_addr(&self, dns: &Dns) -> SocketAddr;
}

impl Dns {
    pub(crate) fn new(addrs: IpSubnetIter) -> Dns {
        Dns {
            addrs,
            names: IndexMap::new(),
        }
    }

    pub(crate) fn register(&mut self, addr: impl ToIpAddrs) -> HostAddrs {
        addr.register(self)
    }

    pub(crate) fn lookup(&self, addr: impl ToIpAddrs) -> Vec<IpAddr> {
        addr.to_ip_addrs(self)
    }

    pub(crate) fn reverse(&self, addr: IpAddr) -> Option<&str> {
        self.names
            .iter()
            .find(|(_, v)| v.contains(addr))
            .map(|v| v.0.as_str())
    }
}

impl ToIpAddrs for String {
    fn to_ip_addrs(&self, dns: &Dns) -> Vec<IpAddr> {
        (&self[..]).to_ip_addrs(dns)
    }

    fn register(&self, dns: &mut Dns) -> HostAddrs {
        (&self[..]).register(dns)
    }
}

impl<'a> ToIpAddrs for &'a str {
    fn to_ip_addrs(&self, dns: &Dns) -> Vec<IpAddr> {
        if let Ok(ipaddr) = self.parse() {
            return vec![ipaddr];
        }

        dns.names
            .get(*self)
            .map(|v| v.to_vec())
            .unwrap_or(Vec::new())
    }

    fn register(&self, dns: &mut Dns) -> HostAddrs {
        if let Ok(ipaddr) = self.parse::<IpAddr>() {
            return ipaddr.register(dns);
        }

        // Register new node with unique domain name
        assert!(
            !dns.names.contains_key(*self),
            "Cannot register multiple nodes under the same name"
        );

        let addrs = dns.addrs.next();
        dns.names.insert(self.to_string(), addrs.clone());
        addrs
    }
}

impl ToIpAddrs for IpAddr {
    fn to_ip_addrs(&self, _: &Dns) -> Vec<IpAddr> {
        vec![*self]
    }

    fn register(&self, dns: &mut Dns) -> HostAddrs {
        match self {
            IpAddr::V4(addr) => addr.register(dns),
            IpAddr::V6(addr) => addr.register(dns),
        }
    }
}

impl ToIpAddrs for Ipv4Addr {
    fn to_ip_addrs(&self, _: &Dns) -> Vec<IpAddr> {
        vec![IpAddr::V4(*self)]
    }

    fn register(&self, dns: &mut Dns) -> HostAddrs {
        let mut addrs = dns.addrs.next();
        addrs.override_addr(IpAddr::V4(*self));
        addrs
    }
}

impl ToIpAddrs for Ipv6Addr {
    fn to_ip_addrs(&self, _: &Dns) -> Vec<IpAddr> {
        vec![IpAddr::V6(*self)]
    }

    fn register(&self, dns: &mut Dns) -> HostAddrs {
        let mut addrs = dns.addrs.next();
        addrs.override_addr(IpAddr::V6(*self));
        addrs
    }
}

#[cfg(feature = "regex")]
impl ToIpAddrs for Regex {
    fn to_ip_addrs(&self, dns: &Dns) -> Vec<IpAddr> {
        #[allow(clippy::needless_collect)]
        let hosts = dns.names.keys().cloned().collect::<Vec<_>>();
        hosts
            .into_iter()
            .filter_map(|h| self.is_match(&h).then(|| h.to_ip_addr(dns)))
            .collect::<Vec<_>>()
    }
}

// Hostname and port
impl ToSocketAddrs for (String, u16) {
    fn to_socket_addr(&self, dns: &Dns) -> SocketAddr {
        (&self.0[..], self.1).to_socket_addr(dns)
    }
}

impl<'a> ToSocketAddrs for (&'a str, u16) {
    fn to_socket_addr(&self, dns: &Dns) -> SocketAddr {
        // When IP address is passed directly as a str.
        if let Ok(ip) = self.0.parse::<IpAddr>() {
            return (ip, self.1).into();
        }

        match dns.names.get(self.0) {
            Some(ip) => (ip[0], self.1).into(), // TODO
            None => panic!("no ip address found for a hostname: {}", self.0),
        }
    }
}

impl ToSocketAddrs for SocketAddr {
    fn to_socket_addr(&self, _: &Dns) -> SocketAddr {
        *self
    }
}

impl ToSocketAddrs for SocketAddrV4 {
    fn to_socket_addr(&self, _: &Dns) -> SocketAddr {
        SocketAddr::V4(*self)
    }
}

impl ToSocketAddrs for SocketAddrV6 {
    fn to_socket_addr(&self, _: &Dns) -> SocketAddr {
        SocketAddr::V6(*self)
    }
}

impl ToSocketAddrs for (IpAddr, u16) {
    fn to_socket_addr(&self, _: &Dns) -> SocketAddr {
        (*self).into()
    }
}

impl ToSocketAddrs for (Ipv4Addr, u16) {
    fn to_socket_addr(&self, _: &Dns) -> SocketAddr {
        (*self).into()
    }
}

impl ToSocketAddrs for (Ipv6Addr, u16) {
    fn to_socket_addr(&self, _: &Dns) -> SocketAddr {
        (*self).into()
    }
}

impl<T: ToSocketAddrs + ?Sized> ToSocketAddrs for &T {
    fn to_socket_addr(&self, dns: &Dns) -> SocketAddr {
        (**self).to_socket_addr(dns)
    }
}

impl ToSocketAddrs for str {
    fn to_socket_addr(&self, dns: &Dns) -> SocketAddr {
        let socketaddr: Result<SocketAddr, _> = self.parse();

        if let Ok(s) = socketaddr {
            return s;
        }

        // Borrowed from std
        // https://github.com/rust-lang/rust/blob/1b225414f325593f974c6b41e671a0a0dc5d7d5e/library/std/src/sys_common/net.rs#L175
        macro_rules! try_opt {
            ($e:expr, $msg:expr) => {
                match $e {
                    Some(r) => r,
                    None => panic!("Unable to parse dns: {}", $msg),
                }
            };
        }

        // split the string by ':' and convert the second part to u16
        let (host, port_str) = try_opt!(self.rsplit_once(':'), "invalid socket address");
        let port: u16 = try_opt!(port_str.parse().ok(), "invalid port value");

        (host, port).to_socket_addr(dns)
    }
}

impl ToSocketAddrs for String {
    fn to_socket_addr(&self, dns: &Dns) -> SocketAddr {
        self.as_str().to_socket_addr(dns)
    }
}

mod sealed {

    pub trait Sealed {}

    impl<T: ?Sized> Sealed for T {}
}

// #[cfg(test)]
// mod tests {
//     use crate::{dns::Dns, ip::IpSubnet, ToSocketAddrs};
//     use std::net::Ipv4Addr;

//     #[test]
//     fn parse_str() {
//         let mut dns = Dns::new(IpSubnet::default().iter());
//         let generated_addr = dns.lookup("foo");

//         let hostname_port = "foo:5000".to_socket_addr(&dns);
//         let ipv4_port = "127.0.0.1:5000";
//         let ipv6_port = "[::1]:5000";

//         assert_eq!(
//             hostname_port,
//             format!("{generated_addr}:5000").parse().unwrap()
//         );
//         assert_eq!(ipv4_port.to_socket_addr(&dns), ipv4_port.parse().unwrap());
//         assert_eq!(ipv6_port.to_socket_addr(&dns), ipv6_port.parse().unwrap());
//     }

//     #[test]
//     fn raw_value_parsing() {
//         // lookups of raw ip addrs should be consistent
//         // between to_ip_addr() and to_socket_addr()
//         // for &str and IpAddr
//         let mut dns = Dns::new(IpSubnet::default().iter());
//         let addr = dns.lookup(Ipv4Addr::new(192, 168, 2, 2));
//         assert_eq!(addr, Ipv4Addr::new(192, 168, 2, 2));

//         let addr = dns.lookup("192.168.3.3");
//         assert_eq!(addr, Ipv4Addr::new(192, 168, 3, 3));

//         let addr = "192.168.3.3:0".to_socket_addr(&dns);
//         assert_eq!(addr.ip(), Ipv4Addr::new(192, 168, 3, 3));
//     }
// }
