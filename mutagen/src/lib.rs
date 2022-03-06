//! A small crate with big macros to make all the tedious bits of generation and mutation less cumbersome.
//!
//! # Generatable
//!
//! When derived on a struct, it will construct it by recursively generating its fields.
//!
//! When derived on an enum, it will choose a variant at random and recursively generate its fields.
//!
//! # Mutatable
//!
//! When derived on a struct, it will pick a field at random
//!
//! When derived on an enum, it requires [Generatable] to also be implemented for all fields, unless mut_reroll is 0.
//! It will then choose whether to re-roll a new variant with probability mut_reroll, or to mutate its current variant.
//!
//! # Attributes
//!
//! This crate makes extensive use of key-value pairs in attributes to customize the behaviour of its derive macros.
//! Key-value pairs are always contained inside a #[mutagen()], as shown in the example below.
//! Both floating point literals and function names are allowed as values.
//! When a function name is used, its signature should be `fn(&mutagen::State) -> f64`
//!
//! ```rust
//! use mutagen::{Generatable, Mutatable};
//!
//! #[derive(Generatable, Mutatable)]
//! #[mutagen(gen_arg = type (), mut_arg = type (), mut_reroll = 0.78)]
//! enum Foo {
//!   // Bar is 10 times as likely as Baz or Bax,
//!   // but it always rerolls into a different one when mutating
//!   #[mutagen(gen_weight = 10.0, mut_reroll = 1.0)]
//!   Bar,
//!
//!   // Baz never changes into a different variant when mutating
//!   #[mutagen(mut_reroll = 0.0)]
//!   Baz(Baz),
//!
//!   // All other variants have reroll probability of 0.78, as specified on Foo
//!   Bax {
//!      // a mutates twice as often as b
//!      #[mutagen(mut_weight = 0.5)]
//!      a: Baz,
//!
//!      b: Baz,
//!
//!      // c mutates only if it's at depth 2 or deeper
//!      #[mutagen(mut_weight = 1.0)]
//!      c: Baz,
//!
//!      // d doesn't need to implement Generatable nor Mutatable, and will use its Default implementation to generate
//!      #[mutagen(skip)]
//!      d: Vec<u32>,
//!   },
//!
//!   // This variant will never generate, so its fields don't need to implement Generatable
//!   #[mutagen(gen_weight = 0.0)]
//!   Boo(NotGeneratable),
//! }
//!
//! #[derive(Mutatable)]
//! #[mutagen(mut_arg = type ())]
//! struct Boz {
//!   // frob will never mutate, so it doesn't need to implement Mutatable
//!   #[mutagen(mut_weight = 0.0)]
//!   not_mutatable: NotMutatable,
//!
//!   mutatable: Baz,
//! }
//!
//! #[derive(Mutatable)]
//! #[mutagen(mut_arg = type ())]
//! struct NotGeneratable;
//!
//! #[derive(Generatable)]
//! #[mutagen(gen_arg = type ())]
//! struct NotMutatable;
//!
//! #[derive(Generatable, Mutatable)]
//! #[mutagen(gen_arg = type (), mut_arg = type ())]
//! struct Baz;
//! ```
//!
//! **`#[mutagen(gen_weight = 1.0)]`**
//!
//! When applied to an enum variant, it affects how often that variant is generated.
//! By default, all variants have weight 1.
//!
//! Note that when an enum variant has a weight of 0, it will never be generated, so the derived impl
//! will not expect its fields to implement Generatable.
//!
//! **`#[mutagen(mut_weight = 1.0)]`**
//!
//! When applied to a struct field, it affects how often that field is mutated.
//! By default, all fields have weight 1.
//!
//! Note that when a field has a weight of 0, it will never be mutated, so the derived impl
//! will not expect its fields to implement Mutatable.
//!
//! **`#[mutagen(mut_reroll = 0.5)]`**
//!
//! When applied to an enum, it sets the probability that an enum variant will be rerolled.
//! When applied to an enum variant, it overrides the value set on the enum for that particular variant.
//!
//! **`#[mutagen(skip)]`**
//!
//! When applied to a field, it is equivalent to `#[mutagen(mut_weight = 0.0)]`, and in addition its
//! type does not need to implement Generatable. Instead, the derived impl will use the type's `Default` impl.

#[doc(no_inline)]
/// The `rand` dependency, re-exported for ease of access
pub use rand;

#[doc(hidden)]
pub use mutagen_derive::*;

use std::{borrow::Cow, ops::DerefMut, rc::Rc, sync::Arc};

use rand::Rng;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A trait denoting that the type may be used as an argument to the other various mutagen traits
/// You should also implement [crate::Reborrow]
pub trait State: Sized {
    /// This function will be called in the derived impls whenever they recurse down a struct or struct enum
    /// The default implementation does nothing - types can implement this.
    fn deepen(&mut self) {}

    /// Trivial utility method that applies `deepen()` and returns self.
    /// Types shouldn't need to implement this
    fn deepened(mut self) -> Self {
        self.deepen();
        self
    }

    /// Hook for profiling events
    fn handle_event(&mut self, _event: Event) {}
}

impl State for () {}

/// A trait denoting that the type may be randomly generated
///
/// For more information, consult the [crate docs](crate).
pub trait Generatable<'a>: Sized {
    type GenArg: State + 'a;

    /// Convenience shorthand for `Self::generate_rng(&mut rand::thread_rng())`
    fn generate(arg: Self::GenArg) -> Self {
        Self::generate_rng(&mut rand::thread_rng(), arg)
    }

    /// The main required method for generation
    fn generate_rng<R: Rng + ?Sized>(rng: &mut R, arg: Self::GenArg) -> Self;
}

impl<'a, T: Generatable<'a>> Generatable<'a> for Box<T> {
    type GenArg = T::GenArg;

    fn generate_rng<R: Rng + ?Sized>(rng: &mut R, arg: Self::GenArg) -> Self {
        Box::new(T::generate_rng(rng, arg))
    }
}

impl<'a, T: Generatable<'a>> Generatable<'a> for Rc<T> {
    type GenArg = T::GenArg;

    fn generate_rng<R: Rng + ?Sized>(rng: &mut R, arg: Self::GenArg) -> Self {
        Rc::new(T::generate_rng(rng, arg))
    }
}

impl<'a, T: Generatable<'a>> Generatable<'a> for Arc<T> {
    type GenArg = T::GenArg;

    fn generate_rng<R: Rng + ?Sized>(rng: &mut R, arg: Self::GenArg) -> Self {
        Arc::new(T::generate_rng(rng, arg))
    }
}

/// A trait denoting that the type may be randomly mutated
///
/// # Derive
/// When derived on a struct, it will randomly pick a field to mutate and call that field's [`mutate()`](crate::Mutatable::mutate)
///
/// When derived on an enum, it requires the enum to also implement [Generatable](crate::Generatable).
/// It will randomly choose between mutating a different variant, in which case it will generate it with [Generate](crate::Generatable),
/// or it will mutate the contents of its current variant.
///
/// ## Attributes
///
pub trait Mutatable<'a> {
    type MutArg: State + 'a;

    fn mutate(&mut self, arg: Self::MutArg) {
        self.mutate_rng(&mut rand::thread_rng(), arg)
    }

    fn mutate_rng<R: Rng + ?Sized>(&mut self, rng: &mut R, arg: Self::MutArg);
}

impl<'a, T: Mutatable<'a>> Mutatable<'a> for Box<T> {
    type MutArg = T::MutArg;

    fn mutate_rng<R: Rng + ?Sized>(&mut self, rng: &mut R, arg: Self::MutArg) {
        self.deref_mut().mutate_rng(rng, arg)
    }
}

/// A trait denoting that the type may be updated.
///
/// # Derive
/// When derived on a struct, it will call each field's [`update()`](crate::Updatable::update)
///
/// When derived on an enum, it will call the current variant's [`update()`](crate::Updatable::update)
pub trait Updatable<'a> {
    type UpdateArg: State + 'a;

    fn update(&mut self, arg: Self::UpdateArg);
}

impl<'a, T: Updatable<'a>> Updatable<'a> for Box<T> {
    type UpdateArg = T::UpdateArg;

    fn update(&mut self, arg: Self::UpdateArg) {
        self.deref_mut().update(arg)
    }
}

/// A utility trait to derive on types to make calls to
/// [`update_recursively()`](crate::UpdatableRecursively::update_recursively)
/// while recursing down to members
pub trait UpdatableRecursively<'a>: Updatable<'a> {
    fn update_recursively(&mut self, arg: Self::UpdateArg);
}

impl<'a, T: UpdatableRecursively<'a>> UpdatableRecursively<'a> for Box<T> {
    fn update_recursively(&mut self, arg: Self::UpdateArg) {
        self.deref_mut().update_recursively(arg)
    }
}

/// Trait to get around lifetime restrictions with `*Arg` types containing mutable references
/// In short, your `*Arg` types should either be `Copy` (and therefore `'static`) or manually implement `Reborrow` along these lines:
///
/// ```rust
/// use mutagen::Reborrow;
///
/// struct Foo<'a> {
///   some_mut_ref: &'a mut i32,
///   some_ref: &'a i32,
/// }
///
/// impl<'a, 'b: 'a> Reborrow<'a, 'b, Foo<'a>> for Foo<'b> {
///   fn reborrow(&'a mut self) -> Foo<'a> {
///     // NOTE: You CANNOT use Self in this constructor!
///     // Self refers to Foo<'b>, while Foo will correctly infer into Foo<'a>
///     Foo {
///       some_mut_ref: &mut self.some_mut_ref,
///       some_ref: &self.some_ref,
///     }
///   }
/// }
///
/// // That allows us to do stuff like this
/// fn bar(_foo: Foo) {}
///
/// fn several_bars(mut foo: Foo) {
///   bar(Reborrow::reborrow(&mut foo));
///   bar(Reborrow::reborrow(&mut foo));
///   bar(Reborrow::reborrow(&mut foo));
/// }
/// ```
pub trait Reborrow<'a, 'b, T>
where
    'b: 'a,
    Self: 'b,
    T: 'a,
{
    fn reborrow(&'a mut self) -> T;
}

impl<'a, 'b, T> Reborrow<'a, 'b, T> for T
where
    'b: 'a,
    T: Copy + 'static,
{
    fn reborrow(&'a mut self) -> T {
        *self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum EventKind {
    Generate,
    Mutate,
    Update,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Event {
    pub kind: EventKind,
    pub key: Cow<'static, str>,
}

/*
#[cfg(test)]
mod test {
    use super::*;

    #[derive(Generatable, Mutatable, UpdatableRecursively)]
    #[mutagen(gen_arg = type (), mut_arg = type (), update_arg = type ())]
    struct Foo {
        #[mutagen(mut_weight = 10.0)]
        bar: Bar,
        baz: Baz,
        bax: Bax,
        bap: Bap,
    }

    #[derive(Generatable, Mutatable, UpdatableRecursively)]
    #[mutagen(gen_arg = type (), mut_arg = type (), update_arg = type ())]
    struct Bar;

    #[derive(Generatable, Mutatable, UpdatableRecursively)]
    #[mutagen(gen_arg = type (), mut_arg = type (), update_arg = type (), mut_reroll = 0.123)]
    enum Baz {
        #[mutagen(gen_weight = 10.0, mut_reroll = 1.0)]
        Boz,
        Bop(Bar),
        Bof(Bar, Bar),
        Bob {
            bar: Bar,
        },
    }

    #[derive(Generatable, Mutatable, UpdatableRecursively)]
    #[mutagen(gen_arg = type (), mut_arg = type (), update_arg = type ())]
    struct Bax(Bar);

    #[derive(Generatable, Mutatable, UpdatableRecursively)]
    #[mutagen(gen_arg = type (), mut_arg = type (), update_arg = type ())]
    struct Bap(Bar, Bar);
}
*/
