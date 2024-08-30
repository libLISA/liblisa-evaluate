use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

pub trait Id: Copy + Eq + Hash {
    fn from_usize(val: usize) -> Self;
    fn as_index(&self) -> usize;
}

#[derive(Clone)]
pub struct IdMap<T> {
    map: HashMap<String, T>,
    offset: usize,
}

impl<T: Id> Default for IdMap<T> {
    fn default() -> Self {
        Self {
            map: HashMap::new(),
            offset: 0,
        }
    }
}

impl<T: Debug> Debug for IdMap<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.map, f)
    }
}

impl<T: Id> IdMap<T> {
    pub fn get(&mut self, name: String) -> T {
        let num = self.map.len() + self.offset;
        *self.map.entry(name).or_insert(T::from_usize(num))
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len() + self.offset
    }

    pub fn reset_scope(&mut self) {
        self.offset += self.map.len();
        self.map.clear();
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct IndexMap<K, V> {
    data: Vec<Option<V>>,
    _phantom: PhantomData<*const K>,
}

impl<K, V> Default for IndexMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V: Debug> Debug for IndexMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut m = f.debug_map();

        for (index, value) in self.data.iter().enumerate() {
            if let Some(value) = value {
                m.entry(&index, value);
            }
        }

        m.finish()
    }
}

impl<K, V> IndexMap<K, V> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            _phantom: PhantomData,
        }
    }

    fn fill(&mut self, index: usize) {
        while self.data.len() <= index {
            self.data.push(None);
        }
    }

    pub fn map<U>(self, mut f: impl FnMut(V) -> U) -> IndexMap<K, U> {
        IndexMap {
            data: self.data.into_iter().map(|item| item.map(&mut f)).collect(),
            _phantom: PhantomData,
        }
    }

    pub fn as_ref(&self) -> IndexMap<K, &V> {
        IndexMap {
            data: self.data.iter().map(|item| item.as_ref()).collect(),
            _phantom: PhantomData,
        }
    }
}

impl<K: Id, V> IndexMap<K, V> {
    pub fn get_mut(&mut self, id: K) -> &mut Option<V> {
        self.fill(id.as_index());
        &mut self.data[id.as_index()]
    }

    pub fn get(&self, id: K) -> &Option<V> {
        if id.as_index() < self.data.len() {
            &self.data[id.as_index()]
        } else {
            &None
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.data
            .iter()
            .enumerate()
            .flat_map(|(index, val)| val.as_ref().map(|val| (K::from_usize(index), val)))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (K, &mut V)> {
        self.data
            .iter_mut()
            .enumerate()
            .flat_map(|(index, val)| val.as_mut().map(|val| (K::from_usize(index), val)))
    }

    pub fn iter_all(&self) -> impl Iterator<Item = (K, Option<&V>)> {
        self.data
            .iter()
            .enumerate()
            .map(|(index, val)| (K::from_usize(index), val.as_ref()))
    }

    pub fn iter_all_mut(&mut self) -> impl Iterator<Item = (K, Option<&mut V>)> {
        self.data
            .iter_mut()
            .enumerate()
            .map(|(index, val)| (K::from_usize(index), val.as_mut()))
    }

    pub fn contains_key(&self, key: K) -> bool {
        self.get(key).is_some()
    }

    pub fn keys(&self) -> impl Iterator<Item = K> + '_ {
        self.iter().map(|(k, _)| k)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> + '_ {
        self.iter().map(|(_, v)| v)
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> + '_ {
        self.iter_mut().map(|(_, v)| v)
    }
}

impl<K: Id, V> FromIterator<(K, V)> for IndexMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut result = Self::new();
        for (k, v) in iter {
            result[k] = Some(v);
        }

        result
    }
}

impl<K: Id, V> Index<K> for IndexMap<K, V> {
    type Output = Option<V>;

    fn index(&self, index: K) -> &Self::Output {
        self.get(index)
    }
}

impl<K: Id, V> IndexMut<K> for IndexMap<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.get_mut(index)
    }
}

impl<'a, K: Id, V> Index<&'a K> for IndexMap<K, V> {
    type Output = Option<V>;

    fn index(&self, index: &'a K) -> &Self::Output {
        self.get(*index)
    }
}

impl<'a, K: Id, V> IndexMut<&'a K> for IndexMap<K, V> {
    fn index_mut(&mut self, index: &'a K) -> &mut Self::Output {
        self.get_mut(*index)
    }
}
