use std::{
    error::Error,
    fmt::{Debug, Display},
    net::{IpAddr, Ipv4Addr, Ipv6Addr},
    ops::Deref,
    str::FromStr,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostAddrs {
    addrs: Vec<IpAddr>,
    subnets: Vec<IpSubnet>,
}

impl HostAddrs {
    pub(crate) fn contains(&self, addr: IpAddr) -> bool {
        for &bound in &self.addrs {
            if bound == addr {
                return true;
            }
        }
        false
    }

    pub fn override_addr(&mut self, addr: IpAddr) {
        for i in 0..self.len() {
            if self.subnets[i].contains(addr) {
                self.addrs[i] = addr;
                return;
            }
        }

        panic!("Cannot assign addr {addr} to node, since this address is not in any defined subnet")
    }

    pub(crate) fn src_addr_for(&self, dst: IpAddr) -> IpAddr {
        for i in 0..self.len() {
            if self.subnets[i].contains(dst) {
                return self.addrs[i];
            }
        }

        if dst.is_loopback() {
            return dst;
        }

        unreachable!("cannot find applicable addr, dst is {dst}")
    }
}

impl Display for HostAddrs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.addrs)
    }
}

impl Deref for HostAddrs {
    type Target = [IpAddr];
    fn deref(&self) -> &Self::Target {
        &self.addrs
    }
}

impl From<(Vec<IpAddr>, Vec<IpSubnet>)> for HostAddrs {
    fn from(value: (Vec<IpAddr>, Vec<IpSubnet>)) -> Self {
        HostAddrs {
            addrs: value.0,
            subnets: value.1,
        }
    }
}

#[derive(Clone)]
pub struct IpSubnets {
    subnets: Vec<IpSubnet>,
}

impl IpSubnets {
    pub fn new() -> Self {
        Self {
            subnets: Vec::new(),
        }
    }

    pub fn add(&mut self, subnet: IpSubnet) {
        assert!(
            !self.intersects(&subnet),
            "Cannot add subnet {subnet} to simulation, intersects with existing subnet"
        );
        self.subnets.push(subnet);
    }

    fn intersects(&self, subnet: &IpSubnet) -> bool {
        for existing in &self.subnets {
            if existing.intersects(subnet) {
                return true;
            }
        }
        false
    }

    pub(crate) fn addrs_iter(self) -> IpSubnetIter {
        IpSubnetIter {
            subnets: self,
            state: 1,
        }
    }
}

impl Default for IpSubnets {
    fn default() -> Self {
        IpSubnets {
            subnets: vec![Ipv4Subnet::default().into(), Ipv6Subnet::default().into()],
        }
    }
}

impl Deref for IpSubnets {
    type Target = [IpSubnet];
    fn deref(&self) -> &Self::Target {
        &self.subnets
    }
}

impl FromIterator<IpSubnet> for IpSubnets {
    fn from_iter<T: IntoIterator<Item = IpSubnet>>(iter: T) -> Self {
        let mut subnets = IpSubnets::new();
        for item in iter {
            subnets.add(item)
        }
        subnets
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IpSubnet {
    V4(Ipv4Subnet),
    V6(Ipv6Subnet),
}

impl IpSubnet {
    pub fn contains(&self, addr: IpAddr) -> bool {
        match (self, addr) {
            (Self::V4(subnet), IpAddr::V4(addr)) => subnet.contains(addr),
            (Self::V6(subnet), IpAddr::V6(addr)) => subnet.contains(addr),
            _ => false,
        }
    }

    fn intersects(&self, subnet: &IpSubnet) -> bool {
        use IpSubnet::*;
        match (self, subnet) {
            (V4(lhs), V4(rhs)) => lhs.intersects(rhs),
            (V6(lhs), V6(rhs)) => lhs.intersects(rhs),
            _ => false,
        }
    }
}

impl FromStr for IpSubnet {
    type Err = Box<dyn Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ipv4Subnet::from_str(s)
            .map(|net| IpSubnet::V4(net))
            .or_else(|_| Ipv6Subnet::from_str(s).map(|net| IpSubnet::V6(net)))
    }
}

impl Display for IpSubnet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::V4(subnet) => write!(f, "{subnet}"),
            Self::V6(subnet) => write!(f, "{subnet}"),
        }
    }
}

impl From<Ipv4Subnet> for IpSubnet {
    fn from(subnet: Ipv4Subnet) -> IpSubnet {
        IpSubnet::V4(subnet)
    }
}

impl From<Ipv6Subnet> for IpSubnet {
    fn from(subnet: Ipv6Subnet) -> IpSubnet {
        IpSubnet::V6(subnet)
    }
}

/// An Ipv4 subnet, defining a range of availale Ipv4 addresses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv4Subnet {
    prefix: Ipv4Addr,
    mask: Ipv4Addr,
}

impl Ipv4Subnet {
    /// A new instance of `Ipv4Network`.
    ///
    /// The provided prefix is truncated according to the
    /// prefixlen.
    ///
    /// # Panics
    ///
    /// This function panic if the prefixlen exceeds 32.
    pub fn new(prefix: Ipv4Addr, prefixlen: usize) -> Ipv4Subnet {
        assert!(
            prefixlen <= 32,
            "prefix lengths greater than 32 are not possible in Ipv4 networks"
        );
        let mask = Ipv4Addr::from(!(u32::MAX >> prefixlen));
        let prefix = Ipv4Addr::from(u32::from(prefix) & u32::from(mask));
        Ipv4Subnet { prefix, mask }
    }

    pub fn contains(&self, addr: Ipv4Addr) -> bool {
        u32::from(self.prefix) == u32::from(addr) & u32::from(self.mask)
    }

    fn intersects(&self, subnet: &Ipv4Subnet) -> bool {
        let lhs_start = u32::from(self.prefix);
        let lhs_end = u32::from(self.prefix) | !u32::from(self.mask);
        let rhs_start = u32::from(subnet.prefix);
        let rhs_end = u32::from(subnet.prefix) | !u32::from(subnet.mask);

        lhs_start <= rhs_end && rhs_start <= lhs_end
    }
}

#[derive(Debug)]
pub struct Ipv4SubnetParsingError;

impl Display for Ipv4SubnetParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Self as Debug>::fmt(self, f)
    }
}
impl Error for Ipv4SubnetParsingError {}

impl FromStr for Ipv4Subnet {
    type Err = Box<dyn Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let Some((prefix, len)) = s.split_once('/') else {
            return Err(Box::new(Ipv4SubnetParsingError))
        };

        let prefix = prefix.parse()?;
        let prefixlen = len.parse()?;
        Ok(Ipv4Subnet::new(prefix, prefixlen))
    }
}

impl Display for Ipv4Subnet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.prefix, u32::from(self.mask).leading_ones())
    }
}

impl Default for Ipv4Subnet {
    fn default() -> Self {
        Ipv4Subnet::new(Ipv4Addr::new(192, 168, 0, 0), 16)
    }
}

/// An Ipv6 subnet, defining a range of availale Ipv6 addresses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv6Subnet {
    prefix: Ipv6Addr,
    mask: Ipv6Addr,
}

impl Ipv6Subnet {
    /// A new instance of `Ipv6Network`.
    ///
    /// The provided prefix is truncated according to the
    /// prefixlen.
    ///
    /// # Panics
    ///
    /// This function panic if the prefixlen exceeds 128.
    pub fn new(prefix: Ipv6Addr, prefixlen: usize) -> Ipv6Subnet {
        assert!(
            prefixlen <= 128,
            "prefix lengths greater than 128 are not possible in Ipv6 networks"
        );
        let mask = Ipv6Addr::from(!(u128::MAX >> prefixlen));
        let prefix = Ipv6Addr::from(u128::from(prefix) & u128::from(mask));
        Ipv6Subnet { prefix, mask }
    }

    pub fn contains(&self, addr: Ipv6Addr) -> bool {
        u128::from(self.prefix) == u128::from(addr) & u128::from(self.mask)
    }

    fn intersects(&self, subnet: &Ipv6Subnet) -> bool {
        let lhs_start = u128::from(self.prefix);
        let lhs_end = u128::from(self.prefix) | !u128::from(self.mask);
        let rhs_start = u128::from(subnet.prefix);
        let rhs_end = u128::from(subnet.prefix) | !u128::from(subnet.mask);

        lhs_start <= rhs_end && rhs_start <= lhs_end
    }
}

#[derive(Debug)]
pub struct Ipv6SubnetParsingError;

impl Display for Ipv6SubnetParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Self as Debug>::fmt(self, f)
    }
}
impl Error for Ipv6SubnetParsingError {}

impl FromStr for Ipv6Subnet {
    type Err = Box<dyn Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let Some((prefix, len)) = s.split_once('/') else {
            return Err(Box::new(Ipv4SubnetParsingError))
        };

        let prefix = prefix.parse()?;
        let prefixlen = len.parse()?;
        Ok(Ipv6Subnet::new(prefix, prefixlen))
    }
}

impl Display for Ipv6Subnet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}/{}",
            self.prefix,
            u128::from(self.mask).leading_ones()
        )
    }
}

impl Default for Ipv6Subnet {
    fn default() -> Self {
        Ipv6Subnet::new(
            Ipv6Addr::from(0xfe80_0000_0000_0000_0000_0000_0000_0000),
            64,
        )
    }
}

pub(crate) struct IpSubnetIter {
    subnets: IpSubnets,
    state: u128,
}

impl IpSubnetIter {
    pub(crate) fn next(&mut self) -> HostAddrs {
        let mut vec = Vec::with_capacity(self.subnets.len());
        for subnet in self.subnets.iter() {
            match subnet {
                IpSubnet::V4(subnet) => {
                    let host = self.state as u32 & !u32::from(subnet.mask);
                    let addr = Ipv4Addr::from(host | u32::from(subnet.prefix));
                    vec.push(addr.into());
                }
                IpSubnet::V6(subnet) => {
                    let host = self.state & !u128::from(subnet.mask);
                    let addr = Ipv6Addr::from(host | u128::from(subnet.prefix));
                    vec.push(addr.into());
                }
            }
        }

        self.state = self.state.wrapping_add(1);
        HostAddrs::from((vec, self.subnets.to_vec()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn default_subnets_manually() {
        let mut subnets = IpSubnets::new();
        subnets.add("192.168.0.0/16".parse().unwrap());
        subnets.add("fe80::/64".parse().unwrap());

        assert_eq!(subnets.len(), 2);
    }

    #[test]
    #[should_panic = "Cannot add subnet 192.0.0.0/8 to simulation, intersects with existing subnet"]
    fn overlapping_subnets() {
        let mut subnets = IpSubnets::new();
        subnets.add("192.168.0.0/16".parse().unwrap());
        subnets.add("192.0.0.0/8".parse().unwrap());
    }

    #[test]
    fn default_subnets() -> Result {
        let mut sim = Builder::new().build();
        sim.client("client", async move {
            assert_eq!(lookup("client").len(), 2);
            assert_eq!(lookup("server").len(), 2);

            assert!(lookup("client").contains(&Ipv4Addr::new(192, 168, 0, 1).into()));
            assert!(lookup("server").contains(&Ipv4Addr::new(192, 168, 0, 2).into()));

            assert!(lookup("client").contains(&Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1).into()));
            assert!(lookup("server").contains(&Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 2).into()));

            Ok(())
        });
        sim.client("server", async move { Ok(()) });

        sim.run()
    }

    #[test]
    fn custom_subnets() -> Result {
        let mut sim = Builder::new()
            .ip_subnets(IpSubnets::from_iter(["10.2.1.0/24"
                .parse::<IpSubnet>()
                .unwrap()]))
            .build();
        sim.client("client", async move {
            assert_eq!(lookup("client").len(), 1);
            assert_eq!(lookup("server").len(), 1);

            assert!(lookup("client").contains(&Ipv4Addr::new(10, 2, 1, 1).into()));
            assert!(lookup("server").contains(&Ipv4Addr::new(10, 2, 1, 2).into()));

            Ok(())
        });
        sim.client("server", async move { Ok(()) });

        sim.run()
    }

    #[test]
    #[should_panic = "Cannot assign addr 30.0.0.0 to node, since this address is not in any defined subnet"]
    fn subnet_denies_invalid_addr_v4() {
        let mut sim = Builder::new().build();
        sim.client("30.0.0.0", async move { Ok(()) });
    }
}
