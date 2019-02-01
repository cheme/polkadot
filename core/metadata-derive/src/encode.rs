use proc_macro2::{Span, TokenStream};
use syn::{
	Data, Field, Fields, Type,
	Meta, NestedMeta, Lit, Attribute, Variant,
	punctuated::Punctuated,
	spanned::Spanned,
	token::Comma,
};

type FieldsList = Punctuated<Field, Comma>;

fn encode_fields(
	fields: &FieldsList,
	registry: &TokenStream
) -> TokenStream
{
	let recurse = fields.iter().enumerate().map(|(i, f)| {
		let name = f.ident.as_ref().map(|iden| quote! {
			_substrate_metadata::FieldName::Named(stringify!(#iden).into())
		})
		.unwrap_or(quote! {
			_substrate_metadata::FieldName::Unnamed(#i as u32)
		});
		let ty = &f.ty;
		quote_spanned! { f.span() =>
			{
				let type_name = <#ty as _substrate_metadata::EncodeMetadata>::type_name();
				#registry.register(type_name.clone(), <#ty as _substrate_metadata::EncodeMetadata>::type_metadata_kind);
				_substrate_metadata::FieldMetadata {
					name: #name,
					ty: type_name
				}
			}
		}
	});

	quote! {
		_substrate_metadata::TypeMetadataKind::Struct(vec![#( #recurse, )*])
	}
}

pub fn quote(data: &Data, registry: &TokenStream) -> TokenStream {
	let call_site = Span::call_site();
	let res = match *data {
		Data::Struct(ref data) => {
			match data.fields {
				Fields::Named(ref fields) => encode_fields(
					&fields.named,
					registry
				),
				Fields::Unnamed(ref fields) => encode_fields(
					&fields.unnamed,
					registry
				),
				Fields::Unit => quote_spanned! { call_site =>
					_substrate_metadata::TypeMetadataKind::Struct(vec![])
				},
			}
		},
		Data::Enum(ref data) => {
			let recurse = data.variants.iter().enumerate().map(|(i, f)| {
				let name = &f.ident;
				let index = index(f, i);
				match f.fields {
					Fields::Named(ref fields) => {
						let field_name = |ty: &Type| {
							quote_spanned!(call_site => #ty)
						};
						let fields = fields.named
							.iter()
							.map(|f| {
								let ty = field_name(&f.ty);
								let name = &f.ident;
								quote_spanned! { f.span() =>
									{
										let type_name = <#ty as _substrate_metadata::EncodeMetadata>::type_name();
										#registry.register(
											type_name.clone(),
											<#ty as _substrate_metadata::EncodeMetadata>::type_metadata_kind
										);
										_substrate_metadata::FieldMetadata {
											name: _substrate_metadata::FieldName::Named(stringify!(#name).into()),
											ty: type_name
										}
									}
								}
							});

						quote_spanned! { f.span() =>
							_substrate_metadata::EnumVariantMetadata {
								name: stringify!(#name).into(),
								index: #index as u32,
								fields: vec![#( #fields, )*]
							}
						}
					},
					Fields::Unnamed(ref fields) => {
						let field_name = |ty: &Type| {
							quote_spanned!(call_site => #ty)
						};
						let fields = fields.unnamed
							.iter()
							.enumerate()
							.map(|(i, f)| {
								let ty = field_name(&f.ty);
								quote! {
									{
										let type_name = <#ty as _substrate_metadata::EncodeMetadata>::type_name();
										#registry.register(
											type_name.clone(),
											<#ty as _substrate_metadata::EncodeMetadata>::type_metadata_kind
										);
										_substrate_metadata::FieldMetadata {
											name: _substrate_metadata::FieldName::Unnamed(#i as u32),
											ty: type_name
										}
									}
								}
							});

						quote_spanned! { f.span() =>
							_substrate_metadata::EnumVariantMetadata {
								name: stringify!(#name).into(),
								index: #index as u32,
								fields: vec![#( #fields, )*]
							}
						}
					},
					Fields::Unit => {
						quote_spanned! { f.span() =>
							_substrate_metadata::EnumVariantMetadata {
								name: stringify!(#name).into(),
								index: #index as u32,
								fields: Vec::new()
							}
						}
					},
				}
			});

			quote! {
				_substrate_metadata::TypeMetadataKind::Enum(vec![#( #recurse, )*])
			}
		},
		Data::Union(_) => panic!("Union types are not supported."),
	};
	res
}

fn find_meta_item<'a, F, R, I>(itr: I, pred: F) -> Option<R> where
	F: FnMut(&NestedMeta) -> Option<R> + Clone,
	I: Iterator<Item=&'a Attribute>
{
	itr.filter_map(|attr| {
		let pair = attr.path.segments.first()?;
		let seg = pair.value();
		if seg.ident == "codec" {
			let meta = attr.interpret_meta();
			if let Some(Meta::List(ref meta_list)) = meta {
				return meta_list.nested.iter().filter_map(pred.clone()).next();
			}
		}

		None
	}).next()
}

fn index(v: &Variant, i: usize) -> TokenStream {
	// look for an index in attributes
	let index = find_meta_item(v.attrs.iter(), |meta| {
		if let NestedMeta::Meta(Meta::NameValue(ref nv)) = meta {
			if nv.ident == "index" {
				if let Lit::Str(ref s) = nv.lit {
					let byte: u8 = s.value().parse().expect("Numeric index expected.");
					return Some(byte)
				}
			}
		}

		None
	});

	// then fallback to discriminant or just index
	index.map(|i| quote! { #i })
		.unwrap_or_else(|| v.discriminant
			.as_ref()
			.map(|&(_, ref expr)| quote! { #expr })
			.unwrap_or_else(|| quote! { #i })
		)
}
