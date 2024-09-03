#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, bitcode::Encode, bitcode::Decode)]
pub struct DataGroup {
    id: u32,
}

impl DataGroup {
    pub fn from_u32(id: u32) -> Self {
        Self {
            id,
        }
    }

    pub fn id(&self) -> u32 {
        self.id
    }

    pub fn murmur(&self) -> Murmur {
        let mut h = self.id as i32;
        h ^= h >> 16;
        h *= 0x85ebca6bu32 as i32;
        h ^= h >> 13;
        h *= 0xc2b2ae35u32 as i32;
        h ^= h >> 16;

        Murmur(h as u32)
    }
}

pub struct Murmur(u32);

impl Murmur {
    pub fn as_u32(&self) -> u32 {
        self.0
    }

    pub fn as_hex(&self) -> String {
        format!("{:08x}", self.0)
    }
}
