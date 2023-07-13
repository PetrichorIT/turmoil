use std::{
    error::Error,
    fmt::{Debug, Display},
    net::{IpAddr, Ipv4Addr, Ipv6Addr},
    ops::Deref,
    str::FromStr,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HostAddrPair {
    pub ipv4: Ipv4Addr,
    pub ipv6: Ipv6Addr,
}

impl HostAddrPair {
    pub(crate) fn contains(&self, addr: IpAddr) -> bool {
        self.ipv4 == addr || self.ipv6 == addr
    }
}

impl HostAddrPair {
    pub(crate) fn to_vec(&self) -> Vec<IpAddr> {
        vec![IpAddr::V4(self.ipv4), IpAddr::V6(self.ipv6)]
    }
}

impl Display for HostAddrPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.ipv4, self.ipv6)
    }
}

pub struct IPSubnets {
    subnets: Vec<IPSubnet>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IPSubnet {
    V4(Ipv4Subnet),
    V6(Ipv6Subnet),
}

impl IPSubnets {
    pub fn new() -> Self {
        Self {
            subnets: Vec::new(),
        }
    }

    pub fn add(&mut self, subnet: IPSubnet) {
        assert!(
            !self.intersects(&subnet),
            "Cannot add subnet {subnet} to simulation, intersects with existing subnet"
        )
    }

    fn intersects(&self, subnet: &IPSubnet) -> bool {
        for existing in &self.subnets {
            if existing.intersects(subnet) {
                return true;
            }
        }
        false
    }
}

impl Deref for IPSubnets {
    type Target = [IPSubnet];
    fn deref(&self) -> &Self::Target {
        &self.subnets
    }
}

impl IPSubnet {
    fn intersects(&self, subnet: &IPSubnet) -> bool {
        use IPSubnet::*;
        match (self, subnet) {
            (V4(lhs), V4(rhs)) => lhs.intersects(rhs),
            (V6(lhs), V6(rhs)) => lhs.intersects(rhs),
            _ => false,
        }
    }
}

impl FromStr for IPSubnet {
    type Err = Box<dyn Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ipv4Subnet::from_str(s)
            .map(|net| IPSubnet::V4(net))
            .or_else(|_| Ipv6Subnet::from_str(s).map(|net| IPSubnet::V6(net)))
    }
}

impl Display for IPSubnet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Self as Debug>::fmt(self, f)
    }
}

/// A subnet defining the available addresses in the
/// underlying network.
///
/// The default value is an Ipv4 subnet with addresses
/// in the range `192.168.0.0/16`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct IpSubnet {
    pub v4: Ipv4Subnet,
    pub v6: Ipv6Subnet,
}

impl IpSubnet {
    pub(crate) fn iter(&self) -> IpSubnetIter {
        IpSubnetIter {
            v4_subnet: self.v4,
            v4_state: 1,
            v6_subnet: self.v6,
            v6_state: 1,
        }
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
    v4_subnet: Ipv4Subnet,
    v4_state: u32,
    v6_subnet: Ipv6Subnet,
    v6_state: u128,
}

impl IpSubnetIter {
    pub(crate) fn subnet_v4(&self) -> &Ipv4Subnet {
        &self.v4_subnet
    }

    pub(crate) fn subnet_v6(&self) -> &Ipv6Subnet {
        &self.v6_subnet
    }

    pub(crate) fn next_v4(&mut self) -> Ipv4Addr {
        let host = self.v4_state;
        self.v4_state = host.wrapping_add(1);

        let host_masked = host & !u32::from(self.v4_subnet.mask);
        Ipv4Addr::from(u32::from(self.v4_subnet.prefix) | host_masked)
    }

    pub(crate) fn next_v6(&mut self) -> Ipv6Addr {
        let host = self.v6_state;
        self.v6_state = host.wrapping_add(1);

        let host_masked = host & !u128::from(self.v6_subnet.mask);
        Ipv6Addr::from(u128::from(self.v6_subnet.prefix) | host_masked)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_subnets_manually() {
        let mut subnets = IPSubnets::new();
        subnets.add("192.168.0.0/16".parse().unwrap());
        subnets.add("fe80::/64".parse().unwrap());

        assert_eq!(subnets.len(), 2);
    }
}

// #[cfg(test)]
// mod tests {
//     use super::Ipv6Subnet;
//     use crate::{lookup, Builder, Ipv4Subnet, Result};
//     use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

//     #[test]
//     fn default_ipv4() -> Result {
//         let mut sim = Builder::new().build();
//         sim.client("client", async move {
//             assert_eq!(lookup("client"), IpAddr::V4(Ipv4Addr::new(192, 168, 0, 1)));
//             assert_eq!(lookup("server"), IpAddr::V4(Ipv4Addr::new(192, 168, 0, 2)));
//             Ok(())
//         });
//         sim.client("server", async move { Ok(()) });

//         assert_eq!(
//             sim.lookup("client"),
//             IpAddr::V4(Ipv4Addr::new(192, 168, 0, 1))
//         );
//         assert_eq!(
//             sim.lookup("server"),
//             IpAddr::V4(Ipv4Addr::new(192, 168, 0, 2))
//         );

//         sim.run()
//     }

//     #[test]
//     fn default_ipv6() -> Result {
//         let mut sim = Builder::new().ip_subnet(Ipv6Subnet::default()).build();
//         sim.client("client", async move {
//             assert_eq!(
//                 lookup("client"),
//                 IpAddr::V6(Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1))
//             );
//             assert_eq!(
//                 lookup("server"),
//                 IpAddr::V6(Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 2))
//             );
//             Ok(())
//         });
//         sim.client("server", async move { Ok(()) });

//         assert_eq!(
//             sim.lookup("client"),
//             IpAddr::V6(Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1))
//         );
//         assert_eq!(
//             sim.lookup("server"),
//             IpAddr::V6(Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 2))
//         );

//         sim.run()
//     }

//     #[test]
//     fn custom_ipv4() -> Result {
//         let mut sim = Builder::new()
//             .ip_subnet(Ipv4Subnet::new(Ipv4Addr::new(10, 1, 3, 0), 24))
//             .build();

//         sim.client("a", async move {
//             assert_eq!(lookup("a"), Ipv4Addr::new(10, 1, 3, 1));
//             Ok(())
//         });
//         sim.client("b", async move {
//             assert_eq!(lookup("b"), Ipv4Addr::new(10, 1, 3, 2));
//             Ok(())
//         });
//         sim.client("c", async move {
//             assert_eq!(lookup("c"), Ipv4Addr::new(10, 1, 3, 3));
//             Ok(())
//         });

//         sim.run()
//     }

//     #[test]
//     fn custom_ipv6() -> Result {
//         let mut sim = Builder::new()
//             .ip_subnet(Ipv6Subnet::new(
//                 Ipv6Addr::new(0x2001, 0, 0, 0, 0, 0, 0, 0),
//                 64,
//             ))
//             .build();

//         sim.client("a", async move {
//             assert_eq!(lookup("a"), Ipv6Addr::new(0x2001, 0, 0, 0, 0, 0, 0, 1));
//             Ok(())
//         });
//         sim.client("b", async move {
//             assert_eq!(lookup("b"), Ipv6Addr::new(0x2001, 0, 0, 0, 0, 0, 0, 2));
//             Ok(())
//         });
//         sim.client("c", async move {
//             assert_eq!(lookup("c"), Ipv6Addr::new(0x2001, 0, 0, 0, 0, 0, 0, 3));
//             Ok(())
//         });

//         sim.run()
//     }

//     #[test]
//     #[should_panic = "node address is not contained within the available subnet"]
//     fn subnet_denies_invalid_addr_v4() {
//         let mut sim = Builder::new()
//             .ip_subnet(Ipv4Subnet::new(Ipv4Addr::new(1, 2, 3, 4), 16))
//             .build();

//         sim.client("30.0.0.0", async move { Ok(()) });
//         unreachable!()
//     }

//     #[test]
//     #[should_panic = "node address is not contained within the available subnet"]
//     fn subnet_denies_invalid_addr_v6() {
//         let mut sim = Builder::new()
//             .ip_subnet(Ipv6Subnet::new(
//                 Ipv6Addr::new(0xfc00, 0, 0, 0, 0, 0, 0, 0),
//                 64,
//             ))
//             .build();

//         sim.client("fc00:0001::bc", async move { Ok(()) });
//         unreachable!()
//     }
// }
