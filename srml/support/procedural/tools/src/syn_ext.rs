// Copyright 2017-2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// tag::description[]
//! Extension to syn types, mainly for parsing
// end::description[]

use syn::parse::{Parse, ParseStream, Result};
use syn::token::{CustomKeyword};
use proc_macro2::TokenStream as T2;
use quote::ToTokens;
use std::iter::once;

/// stop parsing here getting remaining token as content
/// Warn duplicate stream (part of)
#[derive(ParseStruct, ToTokensStruct, Debug)]
pub struct StopParse{pub inner: T2}

//#[derive(ParseEnum, ToTokensEnum, Debug)]
#[derive(ParseEnum, ToTokensEnum, Debug)]
pub enum TestEnum {
  Vis(syn::Visibility),
  Brace(Braces<syn::Visibility>, syn::Visibility),
  End,
}

// inner macro really dependant on syn naming convention, no need to export
macro_rules! groups_impl {
    ($name:ident, $tok:ident, $deli:ident, $parse:ident ) => {
 
#[derive(Debug)]
pub struct $name<P> {
  pub token: syn::token::$tok,
  pub content: P,
}

impl<P: Parse> Parse for $name<P> {
  fn parse(input: ParseStream) -> Result<Self> {
    let syn::group::$name { token, content } = syn::group::$parse(input)?;
    let content = content.parse()?;
    Ok($name { token, content, })
  }
}

impl<P: ToTokens> ToTokens for $name<P> {
  fn to_tokens(&self, tokens: &mut T2) {
    let mut inner_stream = T2::new();
    self.content.to_tokens(&mut inner_stream);
    let token_tree: proc_macro2::TokenTree = proc_macro2::Group::new(proc_macro2::Delimiter::$deli, inner_stream).into();
    tokens.extend(once(token_tree));
  }
}
}}

groups_impl!(Braces, Brace, Brace, parse_braces);
groups_impl!(Brackets, Bracket, Bracket, parse_brackets);
groups_impl!(Parens, Paren, Parenthesis, parse_parens);

#[derive(Debug)]
pub struct CustomToken<T>(std::marker::PhantomData<T>);

impl<T: CustomKeyword> Parse for CustomToken<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    let ident: syn::Ident = input.parse()?;

    if ident.to_string().as_str() != T::ident() {
      return Err(syn::parse::Error::new_spanned(ident, "expected another custom token"))
    }
    Ok(CustomToken(std::marker::PhantomData))
  }
}

impl<T: CustomKeyword> ToTokens for CustomToken<T> {
  fn to_tokens(&self, tokens: &mut T2) {
    use std::str::FromStr;
    tokens.extend(T2::from_str(T::ident()).expect("custom keyword should parse to ident"));
  }
}

impl<T: CustomKeyword> CustomKeyword for CustomToken<T> {
  fn ident() -> &'static str { <T as CustomKeyword>::ident() }
  fn display() -> &'static str { <T as CustomKeyword>::display() }
}

#[derive(Debug)]
pub struct PunctuatedInner<P,T,V> {
  pub inner: syn::punctuated::Punctuated<P,T>,
  pub variant: V,
}

#[derive(Debug)]
pub struct NoTrailing;


#[derive(Debug)]
pub struct Trailing;

pub type Punctuated<P,T> = PunctuatedInner<P,T,NoTrailing>;

pub type PunctuatedTrailing<P,T> = PunctuatedInner<P,T,Trailing>;

impl<P: Parse, T: Parse + syn::token::Token> Parse for PunctuatedInner<P,T,Trailing> {
  fn parse(input: ParseStream) -> Result<Self> {
    Ok(PunctuatedInner {
      inner: syn::punctuated::Punctuated::parse_separated_nonempty(input)?,
      variant: Trailing,
    })
  }
}

impl<P: Parse, T: Parse> Parse for PunctuatedInner<P,T,NoTrailing> {
  fn parse(input: ParseStream) -> Result<Self> {
    Ok(PunctuatedInner {
      inner: syn::punctuated::Punctuated::parse_terminated(input)?,
      variant: NoTrailing,
    })
  }
}

impl<P: ToTokens, T: ToTokens, V> ToTokens for PunctuatedInner<P,T,V> {
  fn to_tokens(&self, tokens: &mut T2) {
    self.inner.to_tokens(tokens)
  }
}


/// Note that syn Meta is almost fine for use case (lacks only `ToToken`)
#[derive(Debug, Clone)]
pub struct Meta {
  pub inner: syn::Meta,
}

impl Parse for Meta {
  fn parse(input: ParseStream) -> Result<Self> {
    Ok(Meta {
      inner: syn::Meta::parse(input)?,
    })
  }
}

impl ToTokens for Meta {
  fn to_tokens(&self, tokens: &mut T2) {
    match self.inner {
      syn::Meta::Word(ref ident) => {
        let ident = ident.clone();
        let toks = quote!{
          #[#ident]
        };
        tokens.extend(toks);
      },
      syn::Meta::List(ref l) => l.to_tokens(tokens),
      syn::Meta::NameValue(ref n) => n.to_tokens(tokens),
    }
  }
}

#[derive(Debug)]
pub struct OuterAttributes {
  pub inner: Vec<syn::Attribute>,
}

impl Parse for OuterAttributes {
  fn parse(input: ParseStream) -> Result<Self> {
    let inner = syn::Attribute::parse_outer(input)?;
    Ok(OuterAttributes {
      inner,
    })
  }
}

impl ToTokens for OuterAttributes {
  fn to_tokens(&self, tokens: &mut T2) {
    for att in self.inner.iter() {
      att.to_tokens(tokens);
    }
  }
}

#[derive(Debug)]
pub struct Seq<P> {
  pub inner: Vec<P>,
}

impl<P: Parse> Parse for Seq<P> {
  // Note that it got a double cost!! (like enum)
  fn parse(input: ParseStream) -> Result<Self> {
    let mut inner = Vec::new();
    loop {
      let fork = input.fork();
      let res: Result<P> = fork.parse();
      match res {
        Ok(_item) => {
          // move cursor
          let item: P = input.parse().expect("Same parsing ran before");
          inner.push(item);
        },
        Err(_e) => break,
      }
    }
    Ok(Seq { inner })
  }
}

impl<P: ToTokens> ToTokens for Seq<P> {
  fn to_tokens(&self, tokens: &mut T2) {
    for p in self.inner.iter() {
      p.to_tokens(tokens);
    }
  }
}

pub fn extract_type_option(typ: &syn::Type) -> Option<T2> {
  if let syn::Type::Path(ref path) = typ {
    path.path.segments.last().and_then(|v| {
      if v.value().ident == "Option" {
        if let syn::PathArguments::AngleBracketed(ref a) = v.value().arguments {
          let args = &a.args;
          Some(quote!{ #args })
        } else {
          None
        }
      } else {
        None
      }
    })
  } else {
    None 
  }
}
