/*
 * Copyright (C)2015-2016 Nicolas Cannasse
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */
package hxbitmini;

import haxe.macro.Expr;
import haxe.macro.Type;
import haxe.macro.Context;
using haxe.macro.TypeTools;
using haxe.macro.ComplexTypeTools;

enum PropTypeDesc<PropType> {
	PInt;
	PFloat;
	PBool;
	PString;
	PBytes;
	PSerializable( name : String );
	PEnum( name : String );
	PMap( k : PropType, v : PropType );
	PArray( k : PropType );
	PObj( fields : Array<{ name : String, type : PropType, opt : Bool }> );
	PAlias( k : PropType );
	PVector( k : PropType );
	PNull( t : PropType );
	PUnknown;
	PDynamic;
	PInt64;
	PFlags( t : PropType );
	PStruct;
}

typedef PropType = {
	var d : PropTypeDesc<PropType>;
	var t : ComplexType;
}

class Macros {

	static var IN_ENUM_SER = false;

	public static macro function serializeValue( ctx : Expr, v : Expr ) : Expr {
		var t = Context.typeof(v);
		var pt = getPropType(t);
		if( pt == null ) {
			Context.error("Unsupported serializable type " + t.toString(), v.pos);
			return macro { };
		}
		IN_ENUM_SER = StringTools.startsWith(Context.getLocalClass().toString(), "hxbitmini.enumSer.");
		return withPos(serializeExpr(ctx, v, pt),v.pos);
	}

	public static macro function unserializeValue( ctx : Expr, v : Expr, depth : Int = 0 ) : Expr {
		var t = Context.typeof(v);
		var pt = getPropType(t);
		if( pt == null ) {
			return macro { };
		}
		IN_ENUM_SER = StringTools.startsWith(Context.getLocalClass().toString(), "hxbitmini.enumSer.");
		return withPos(unserializeExpr(ctx, v, pt, depth),v.pos);
	}

	public static macro function getFieldType( v : Expr ) {
		var t = Context.typeof(v);
		var pt = getPropType(t);
		if( pt == null )
			return macro null;
		var v = toFieldType(pt);
		return macro $v{v};
	}

	#if macro

	static function toFieldType( t : PropType ) : Schema.FieldType {
		return switch( t.d ) {
		case PInt64: PInt64;
		case PInt: PInt;
		case PFloat: PFloat;
		case PBool: PBool;
		case PString: PString;
		case PBytes: PBytes;
		case PSerializable(name): PSerializable(name);
		case PEnum(name): PEnum(name);
		case PMap(k, v): PMap(toFieldType(k), toFieldType(v));
		case PArray(v): PArray(toFieldType(v));
		case PObj(fields): PObj([for( f in fields ) { name : f.name, type : toFieldType(f.type), opt : f.opt }]);
		case PAlias(t): return toFieldType(t);
		case PVector(k): PVector(toFieldType(k));
		case PNull(t): PNull(toFieldType(t));
		case PFlags(t): PFlags(toFieldType(t));
		case PStruct: PStruct;
		case PUnknown: PUnknown;
		case PDynamic: PDynamic;
		};
	}

	static function lookupInterface( c : Ref<ClassType>, name : String ) {
		while( true ) {
			var cg = c.get();
			for( i in cg.interfaces ) {
				if( i.t.toString() == name )
					return true;
				if( lookupInterface(i.t, name) )
					return true;
			}
			var sup = cg.superClass;
			if( sup == null )
				break;
			c = sup.t;
		}
		return false;
	}

	static function isSerializable( c : Ref<ClassType> ) {
		return lookupInterface(c, "hxbitmini.Serializable");
	}

	static function isStructSerializable( c : Ref<ClassType> ) {
		return lookupInterface(c, "hxbitmini.StructSerializable");
	}

	static function getPropField( ft : Type, meta : Metadata ) {
		var t = getPropType(ft);
		if( t == null )
			return null;
		for( m in meta) {
			switch( m.name ) {
			case ":s", ":optional":
				//
			default:
				if(m.name.charAt(0) == ":")
					Context.error("Unsupported network metadata", m.pos);
			}
		}
		return t;
	}

	static function getNativePath( e : BaseType ) {
		var name = e.pack.length == 0 ? e.name : e.pack.join(".") + "." + e.name;
		// handle @:native on enum
		for( m in e.meta.get() )
			if( m.name == ":native" && m.params.length == 1 )
				switch( m.params[0].expr ) {
				case EConst(CString(s)): name = s;
				default:
				}
		return name;
	}

	static function getPropType( t : haxe.macro.Type ) : PropType {
		var desc = switch( t ) {
		case TAbstract(a, pl):
			switch( a.toString() ) {
			case "haxe.Int64":
				PInt64;
			case "Float":
				PFloat;
			case "Int","UInt":
				PInt;
			case "Bool":
				PBool;
			case "Map", "haxe.ds.Map":
				var tk = getPropType(pl[0]);
				var tv = getPropType(pl[1]);
				if( tk == null || tv == null )
					return null;
				PMap(tk, tv);
			case "haxe.ds.Vector":
				var tk = getPropType(pl[0]);
				if( tk == null )
					return null;
				PVector(tk);
			case "haxe.EnumFlags":
				var e = getPropType(pl[0]);
				if( e == null ) return null;
				PFlags(e);
			case "Null":
				var p = getPropType(pl[0]);
				if( p != null && !isNullable(p) )
					p = { d : PNull(p), t : TPath( { pack : [], name : "Null", params : [TPType(p.t)] } ) };
				return p;
			case name:
				var t2 = Context.followWithAbstracts(t, true);
				switch( t2 ) {
				case TAbstract(a2, _) if( a2.toString() == name ):
					return null;
				default:
				}
				var pt = getPropType(t2);
				if( pt == null ) return null;
				PAlias(pt);
			}
		case TEnum(e,_):
			PEnum(getNativePath(e.get()));
		case TDynamic(_):
			PDynamic;
		case TAnonymous(a):
			var a = a.get();
			var fields = [];
			for( f in a.fields ) {
				if( f.meta.has(":noSerialize") )
					continue;
				var ft = getPropField(f.type, f.meta.get());
				if( ft == null ) return null;
				fields.push( { name : f.name, type : ft, opt : f.meta.has(":optional") } );
			}
			PObj(fields);
		case TInst(c, pl):
			switch( c.toString() ) {
			case "String":
				PString;
			case "Array":
				var at = getPropType(pl[0]);
				if( at == null ) return null;
				PArray(at);
			case "haxe.ds.IntMap":
				var vt = getPropType(pl[0]);
				if( vt == null ) return null;
				PMap({ t : macro : Int, d : PInt }, vt);
			case "haxe.ds.StringMap":
				var vt = getPropType(pl[0]);
				if( vt == null ) return null;
				PMap({ t : macro : String, d : PString }, vt);
			case "haxe.io.Bytes":
				PBytes;
			default:
				if( isSerializable(c) )
					PSerializable(getNativePath(c.get()));
				else if( isStructSerializable(c) )
					PStruct;
				else
					return null;
			}
		case TType(td, pl):
			switch( td.toString() ) {
			case "Null":
				var p = getPropType(pl[0]);
				if( p != null && !isNullable(p) )
					p = { d : PNull(p), t : TPath( { pack : [], name : "Null", params : [TPType(p.t)] } ) };
				return p;
			default:
				var p = getPropType(Context.follow(t, true));
				if( p != null )
					p.t = t.toComplexType(); // more general, still identical
				return p;
			}
		default:
			return null;
		}
		var p : PropType = {
			d : desc,
			t : t.toComplexType(),
		};
		return p;
	}

	static function isNullable( t : PropType ) {
		switch( t.d ) {
		case PInt, PFloat, PBool, PFlags(_):
			return false;
		case PAlias(t):
			return isNullable(t);
		// case PInt64: -- might depend on the platform ?
		default:
			return true;
		}
	}

	static function toType( t : ComplexType ) : Type {
		return Context.typeof(macro (null:$t));
	}

	static function serializeExpr( ctx : Expr, v : Expr, t : PropType, skipCheck = false ) {

		switch( t.d ) {
		case PInt64:
			return macro $ctx.addInt64($v);
		case PFloat:
			return macro $ctx.addFloat($v);
		case PInt:
			return macro $ctx.addInt($v);
		case PBool:
			return macro $ctx.addBool($v);
		case PBytes:
			return macro $ctx.addBytes($v);
		case PMap(kt, vt):
			var kt = kt.t;
			var vt = vt.t;
			var vk = { expr : EConst(CIdent("k")), pos : v.pos };
			var vv = { expr : EConst(CIdent("v")), pos : v.pos };
			return macro $ctx.addMap($v, function(k:$kt) return hxbitmini.Macros.serializeValue($ctx, $vk), function(v:$vt) return hxbitmini.Macros.serializeValue($ctx, $vv));
		case PEnum(_):
			var et = t.t;
			var ser = "serialize";
			if( IN_ENUM_SER )
				ser += "2";
			return macro (null : hxbitmini.Serializable.SerializableEnum<$et>).$ser($ctx,$v);
		case PObj(fields):
			var nullables = [for( f in fields ) if( isNullable(f.type) ) f];
			var ct = t.t;
			if( nullables.length >= 32 )
				Context.error("Too many nullable fields", v.pos);
			return macro {
				var v : $ct = $v;
				if( v == null )
					$ctx.addByte(0);
				else {
					var fbits = 0;
					$b{[
						for( i in 0...nullables.length ) {
							var name = nullables[i].name;
							macro if( v.$name != null ) fbits |= $v{ 1 << i };
						}
					]};
					$ctx.addInt(fbits + 1);
					$b{[
						for( f in fields ) {
							var nidx = nullables.indexOf(f);
							var name = f.name;
							if( nidx < 0 )
								macro hxbitmini.Macros.serializeValue($ctx, v.$name);
							else
								macro if( fbits & $v{1<<nidx} != 0 ) hxbitmini.Macros.serializeValue($ctx, v.$name);
						}
					]};
				}
			};
		case PString:
			return macro $ctx.addString($v);
		case PArray(t):
			var at = t.t;
			var ve = { expr : EConst(CIdent("e")), pos : v.pos };
			return macro $ctx.addArray($v, function(e:$at) return hxbitmini.Macros.serializeValue($ctx, $ve));
		case PVector(t):
			var at = t.t;
			var ve = { expr : EConst(CIdent("e")), pos : v.pos };
			return macro $ctx.addVector($v, function(e:$at) return hxbitmini.Macros.serializeValue($ctx, $ve));
		case PSerializable(_):
			return macro $ctx.addKnownRef($v);
		case PAlias(t):
			return serializeExpr(ctx, { expr : ECast(v, null), pos : v.pos }, t);
		case PNull(t):
			var e = serializeExpr(ctx, v, t);
			return macro if( $v == null ) $ctx.addByte(0) else { $ctx.addByte(1); $e; };
		case PDynamic:
			return macro $ctx.addDynamic($v);
		case PFlags(t):
			return serializeExpr(ctx, { expr : ECast(v, null), pos : v.pos }, { t : macro : Int, d : PInt });
		case PStruct:
			return macro $ctx.addStruct($v);
		case PUnknown:
			throw "assert";
		}
	}

	static function unserializeExpr( ctx : Expr, v : Expr, t : PropType, depth : Int ) {
		switch( t.d ) {
		case PInt64:
			return macro $v = $ctx.getInt64();
		case PFloat:
			return macro $v = $ctx.getFloat();
		case PInt:
			return macro $v = $ctx.getInt();
		case PBool:
			return macro $v = $ctx.getBool();
		case PBytes:
			return macro $v = $ctx.getBytes();
		case PMap(k,t):
			var kt = k.t;
			var vt = t.t;
			var kname = "k" + depth;
			var vname = "v" + depth;
			var vk = { expr : EConst(CIdent(kname)), pos : v.pos };
			var vv = { expr : EConst(CIdent(vname)), pos : v.pos };
			return macro {
				var $kname : $kt;
				var $vname : $vt;
				$v = $ctx.getMap(function() { hxbitmini.Macros.unserializeValue($ctx, $vk, $v{depth + 1}); return $vk; }, function() { hxbitmini.Macros.unserializeValue($ctx, $vv, $v{depth+1}); return $vv; });
			};
		case PEnum(_):
			var et = t.t;
			var unser = "unserialize";
			if( IN_ENUM_SER )
				unser += "2";
			return macro { var __e : $et; __e = (null : hxbitmini.Serializable.SerializableEnum<$et>).$unser($ctx); $v = __e; }
		case PObj(fields):
			var nullables = [for( f in fields ) if( isNullable(f.type) ) f];
			if( nullables.length >= 32 )
				Context.error("Too many nullable fields", v.pos);
			var ct = t.t;
			return macro {
				var fbits = $ctx.getInt();
				if( fbits == 0 )
					$v = null;
				else {
					fbits--;
					$b{{
						var exprs = [];
						var vars = [];
						for( f in fields ) {
							var nidx = nullables.indexOf(f);
							var name = f.name;
							var ct = f.type.t;
							vars.push( { field : name, expr : { expr : EConst(CIdent(name)), pos:v.pos } } );
							if( nidx < 0 ) {
								exprs.unshift(macro var $name : $ct);
								exprs.push(macro hxbitmini.Macros.unserializeValue($ctx, $i{name}, $v{depth+1}));
							} else {
								exprs.unshift(macro var $name : $ct = null);
								exprs.push(macro if( fbits & $v { 1 << nidx } != 0 ) hxbitmini.Macros.unserializeValue($ctx, $i{name}, $v{depth+1}));
							}
						}
						exprs.push( { expr : EBinop(OpAssign,v, { expr : EObjectDecl(vars), pos:v.pos } ), pos:v.pos } );
						exprs;
					}};
				}
			};
		case PString:
			return macro $v = $ctx.getString();
		case PArray(at):
			var at = at.t;
			var ve = { expr : EConst(CIdent("e")), pos : v.pos };
			var ename = "e" + depth;
			return macro {
				var $ename : $at;
				$v = $ctx.getArray(function() { hxbitmini.Macros.unserializeValue($ctx, $i{ename}, $v{depth+1}); return $i{ename}; });
			};
		case PVector(at):
			var at = at.t;
			var ve = { expr : EConst(CIdent("e")), pos : v.pos };
			var ename = "e" + depth;
			return macro {
				var $ename : $at;
				$v = $ctx.getVector(function() { hxbitmini.Macros.unserializeValue($ctx, $i{ename}, $v{depth+1}); return $i{ename}; });
			};
		case PSerializable(_):
			function loop(t:ComplexType) {
				switch( t ) {
				case TPath( { name : "Null", params:[TPType(t)] } ):
					return loop(t);
				case TPath( p = { params:a } ) if( a.length > 0 ):
					return TPath( { pack : p.pack, name:p.name, sub:p.sub } );
				default:
					return t;
				}
			}
			var cexpr = Context.parse(loop(t.t).toString(), v.pos);
			return macro $v = $ctx.getRef($cexpr,@:privateAccess $cexpr.__clid);
		case PAlias(at):
			var cvt = at.t;
			var vname = "v" + depth;
			return macro {
				var $vname : $cvt;
				${unserializeExpr(ctx,macro $i{vname},at,depth+1)};
				$v = cast $i{vname};
			};
		case PNull(t):
			var e = unserializeExpr(ctx, v, t, depth);
			return macro if( $ctx.getByte() == 0 ) $v = null else $e;
		case PDynamic:
			return macro $v = $ctx.getDynamic();
		case PFlags(_):
			return macro {
				var v : Int;
				${unserializeExpr(ctx,macro v,{ t : macro : Int, d : PInt },depth + 1)};
				$v = ${macro new haxe.EnumFlags(v)};
			};
		case PStruct:
			return macro $v = $ctx.getStruct();
		case PUnknown:
			throw "assert";
		}
	}

	static function withPos( e : Expr, p : Position ) {
		e.pos = p;
		haxe.macro.ExprTools.iter(e, function(e) withPos(e, p));
		return e;
	}

	public static function buildSerializable() {
		var cl = Context.getLocalClass().get();
		if( cl.isInterface || Context.defined("display") )
			return null;
		var fields = Context.getBuildFields();
		var toSerialize = [];
		var addCustomSerializable = false;
		var addCustomUnserializable = false;

		var sup = cl.superClass;
		var isSubSer = sup != null && isSerializable(sup.t);
		var hasNonSerializableParent = sup != null && !isSerializable(sup.t);

		for( f in fields ) {
			// has already been processed
			if( f.name == "__clid" )
				return null;
			if( f.name == "customSerialize" && ( f.access.indexOf(AOverride) < 0 || hasNonSerializableParent ) ) {
				addCustomSerializable = true;
			}
			if( f.name == "customUnserialize" && ( f.access.indexOf(AOverride) < 0 || hasNonSerializableParent ) ) {
				addCustomUnserializable = true;
			}
			if( f.meta == null ) continue;
			for( meta in f.meta )
				if( meta.name == ":s" ) {
					toSerialize.push({ f : f, m : meta });
					break;
				}
		}

		if( cl.meta.has(":serializeSuperClass") ) {
			if( toSerialize.length != 0 || !isSubSer )
				Context.error("Cannot use serializeSuperClass on this class", cl.pos);
			return null;
		}

		if( addCustomSerializable != addCustomUnserializable ) {
			Context.error("customSerialize and customUnserialize must both exist or both be removed!",cl.pos);
		}

		var fieldsInits = [];
		for( f in fields ) {
			if( f.access.indexOf(AStatic) >= 0 ) continue;
			switch( f.kind ) {
			case FVar(_, e), FProp(_, _, _, e) if( e != null ):
				// before unserializing
				fieldsInits.push({ expr : EBinop(OpAssign,{ expr : EConst(CIdent(f.name)), pos : e.pos },e), pos : e.pos });
			default:
			}
		}

		var pos = Context.currentPos();
		// todo : generate proper generic static var ?
		// this is required for fixing conflicting member var / package name
		var useStaticSer = cl.params.length == 0;
		var el = [], ul = [];
		for( f in toSerialize ) {
			var fname = f.f.name;
			var ef = useStaticSer ? macro __this.$fname : macro this.$fname;
			el.push(withPos(macro hxbitmini.Macros.serializeValue(__ctx,$ef),f.f.pos));
			ul.push(withPos(macro hxbitmini.Macros.unserializeValue(__ctx, $ef),f.f.pos));
		}

		var metadata = [{ name : ":noCompletion", pos : pos },{ name : ":keep", pos : pos }];
		var access = [APublic];
		if( isSubSer )
			access.push(AOverride);

		var clName = StringTools.endsWith(cl.module,"."+cl.name) ? cl.module.split(".") : [cl.name];
		fields.push({
			name : "__clid",
			pos : pos,
			access : [AStatic],
			meta : metadata,
			kind : FVar(macro : Int, macro 0),
		});
		fields.push({
			name : "initCLID",
			pos : pos,
			access : [AStatic, APublic],
			meta : metadata,
			kind : FFun({ args : [], ret : null , expr : macro __clid = @:privateAccess hxbitmini.Serializer.registerClass($p{clName}) }),
		});
		fields.push({
			name : "getCLID",
			pos : pos,
			access : access,
			meta : metadata,
			kind : FFun({ args : [], ret : macro : Int, expr : macro return __clid }),
		});

		var needSerialize = toSerialize.length != 0 || !isSubSer || addCustomSerializable;
		var needUnserialize = needSerialize || fieldsInits.length != 0 || addCustomUnserializable;

		if( needSerialize ) {
			if( useStaticSer ) fields.push({
				name : "doSerialize",
				pos : pos,
				access : [AStatic],
				meta : metadata,
				kind : FFun({
					args : [ { name : "__ctx", type : macro : hxbitmini.Serializer }, { name : "__this", type : TPath({ pack : [], name : cl.name }) } ],
					ret : null,
					expr : macro $b{el},
				}),
			});
			fields.push({
				name : "serialize",
				pos : pos,
				access : access,
				kind : FFun({
					args : [ { name : "__ctx", type : macro : hxbitmini.Serializer } ],
					ret : null,
					expr : macro @:privateAccess {
						${ if( isSubSer ) macro super.serialize(__ctx) else macro { } };
						${ if( useStaticSer ) macro doSerialize(__ctx,this) else macro $b{el} };
						${ if( addCustomSerializable ) macro this.customSerialize(__ctx) else macro { } };
					}
				}),
			});
			var schema = [for( s in toSerialize ) {
				var name = s.f.name;
				macro { schema.fieldsNames.push($v{name}); schema.fieldsTypes.push(hxbitmini.Macros.getFieldType(this.$name)); }
			}];
			fields.push({
				name : "getSerializeSchema",
				pos : pos,
				access : access,
				meta : metadata,
				kind : FFun({
					args : [],
					ret : null,
					expr : macro {
						var schema = ${if( isSubSer ) macro super.getSerializeSchema() else macro new hxbitmini.Schema()};
						$b{schema};
						schema.isFinal = hxbitmini.Serializer.isClassFinal(__clid);
						return schema;
					}
				})
			});
		}

		if( fieldsInits.length > 0 || !isSubSer )
			fields.push({
				name : "unserializeInit",
				pos : pos,
				meta : metadata,
				access : access,
				kind : FFun({
					args : [],
					ret : null,
					expr : isSubSer ? macro { super.unserializeInit(); $b{fieldsInits}; } : { expr : EBlock(fieldsInits), pos : pos },
				})
			});

		if( needUnserialize ) {
			var unserExpr = macro @:privateAccess {
				${ if( isSubSer ) macro super.unserialize(__ctx) else macro { } };
				${ if( useStaticSer ) macro doUnserialize(__ctx,this) else macro $b{ul} };
				${ if( addCustomUnserializable ) macro this.customUnserialize(__ctx) else macro { } };
			};

			var unserFound = false;
			for( f in fields )
				if( f.name == "unserialize" ) {
					var found = false;
					function repl(e:Expr) {
						switch( e.expr ) {
						case ECall( { expr : EField( { expr : EConst(CIdent("super")) }, "unserialize") }, [ctx]):
							found = true;
							return macro { var __ctx : hxbitmini.Serializer = $ctx; $unserExpr; }
						default:
							return haxe.macro.ExprTools.map(e, repl);
						}
					}
					switch( f.kind ) {
					case FFun(f):
						f.expr = repl(f.expr);
					default:
					}
					if( !found ) Context.error("Override of unserialize() with no super.unserialize(ctx) found", f.pos);
					unserFound = true;
					break;
				}

			if( useStaticSer ) fields.push({
				name : "doUnserialize",
				pos : pos,
				access : [AStatic],
				meta : metadata,
				kind : FFun({
					args : [ { name : "__ctx", type : macro : hxbitmini.Serializer }, { name : "__this", type : TPath({ pack : [], name : cl.name }) } ],
					ret : null,
					expr : macro $b{ul},
				}),
			});

			if( !unserFound ) fields.push({
				name : "unserialize",
				pos : pos,
				access : access,
				kind : FFun({
					args : [ { name : "__ctx", type : macro : hxbitmini.Serializer } ],
					ret : null,
					expr : unserExpr,
				}),
			});
		}

		return fields;
	}

	public static function buildSerializableEnum() {
		var pt = switch( Context.getLocalType() ) {
		case TInst(_, [pt]): pt;
		default: null;
		}
		if( pt != null )
			pt = Context.follow(pt);
		if( pt != null )
		switch( pt ) {
		case TEnum(e, tparams):
			var e = e.get();
			var name = getNativePath(e).split(".").join("_");
			name = name.charAt(0).toUpperCase() + name.substr(1);
			try {
				return Context.getType("hxbitmini.enumSer." + name);
			} catch( _ : Dynamic ) {
				var pos = Context.currentPos();
				var cases = [], ucases = [], schemaExprs = [];
				if( e.names.length >= 256 )
					Context.error("Too many constructors", pos);
				for( f in e.names ) {
					var c = e.constructs.get(f);
					switch( Context.follow(c.type) ) {
					case TFun(args, _):
						var eargs = [for( a in args ) { var arg = { expr : EConst(CIdent(a.name)), pos : c.pos }; macro hxbitmini.Macros.serializeValue(ctx, $arg); }];
						cases.push({
							values : [{ expr : ECall({ expr : EConst(CIdent(c.name)), pos : pos },[for( a in args ) { expr : EConst(CIdent(a.name)), pos : pos }]), pos : pos }],
							expr : macro {
								ctx.addByte($v{c.index+1});
								$b{eargs};
							}
						});

						var evals = [], etypes = [];
						for( a in args ) {
							var aname = "_" + a.name;
							var at = haxe.macro.TypeTools.applyTypeParameters(a.t,e.params,tparams).toComplexType();
							evals.push(macro var $aname : $at);
							evals.push(macro hxbitmini.Macros.unserializeValue(ctx,$i{aname}));
							etypes.push(macro { var v : $at; hxbitmini.Macros.getFieldType(v); });
						}
						evals.push({ expr : ECall({ expr : EConst(CIdent(c.name)), pos : pos },[for( a in args ) { expr : EConst(CIdent("_"+a.name)), pos : pos }]), pos : pos });
						ucases.push({
							values : [macro $v{c.index+1}],
							expr : { expr : EBlock(evals), pos : pos },
						});
						schemaExprs.push(macro s.fieldsTypes.push(PObj([for( t in [$b{etypes}] ) { name : "", type : t, opt : false }])));

					default:
						if( c.name == "_" ) Context.error("Invalid enum constructor", c.pos);
						cases.push({
							values : [ { expr : EConst(CIdent(c.name)), pos : pos } ],
							expr : macro ctx.addByte($v{c.index+1}),
						});
						ucases.push({
							values : [macro $v{c.index+1}],
							expr : { expr : EConst(CIdent(c.name)), pos : pos },
						});
						schemaExprs.push(macro s.fieldsTypes.push(null));
					}
					schemaExprs.push(macro s.fieldsNames.push($v{f}));
				}
				var t : TypeDefinition = {
					name : name,
					pack : ["hxbitmini","enumSer"],
					kind : TDClass(),
					fields : [
					{
						name : "doSerialize",
						access : [AStatic],
						pos : pos,
						kind : FFun( {
							args : [{ name : "ctx", type : macro : hxbitmini.Serializer },{ name : "v", type : pt.toComplexType() }],
							expr : macro @:privateAccess if( v == null ) ctx.addByte(0) else ${{ expr : ESwitch(macro v,cases,null), pos : pos }},
							ret : macro : Void,
						}),
					},{
						name : "doUnserialize",
						access : [AStatic],
						pos : pos,
						kind : FFun( {
							args : [{ name : "ctx", type : macro : hxbitmini.Serializer }],
							expr : macro @:privateAccess {
								var b = ctx.getByte();
								if( b == 0 )
									return null;
								return ${{ expr : ESwitch(macro b,ucases,macro throw "Invalid enum index "+b), pos : pos }}
							},
							ret : pt.toComplexType(),
						}),

					},{
						name : "getSchema",
						access : [AStatic, APublic],
						meta : [{name:":ifFeature",pos:pos, params:[macro "hxbitmini.Dump.readValue"]}],
						pos : pos,
						kind : FFun( {
							args : [],
							expr : macro { var s = new Schema(); $b{schemaExprs}; return s; },
							ret : macro : hxbitmini.Schema,
						}),
					},{
						name : "serialize",
						access : [AInline, APublic],
						meta : [{name:":extern",pos:pos}],
						pos : pos,
						kind : FFun( {
							args : [{ name : "ctx", type : macro : hxbitmini.Serializer },{ name : "v", type : pt.toComplexType() }],
							expr : macro doSerialize(ctx,v),
							ret : null,
						}),
					},{
						name : "unserialize",
						access : [AInline, APublic],
						meta : [{name:":extern",pos:pos}],
						pos : pos,
						kind : FFun( {
							args : [{ name : "ctx", type : macro : hxbitmini.Serializer }],
							expr : macro return doUnserialize(ctx),
							ret : null,
						}),
					}],
					pos : pos,
				};

				// hack to allow recursion (duplicate serialize/unserialize for recursive usage)
				var tf = Reflect.copy(t.fields[t.fields.length - 2]);
				tf.name += "2";
				t.fields.push(tf);
				var tf = Reflect.copy(t.fields[t.fields.length - 2]);
				tf.name += "2";
				t.fields.push(tf);

				Context.defineType(t);
				return Context.getType("hxbitmini.enumSer." + name);
			}
		default:
		}
		Context.error("Enum expected", Context.currentPos());
		return null;
	}

	static function quickInferType( e : Expr ) {
		if( e == null )
			return null;
		switch( e.expr ) {
		case EConst(CInt(_)):
			return macro : Int;
		case EConst(CFloat(_)):
			return macro : Float;
		case EConst(CString(_)):
			return macro : String;
		case EConst(CIdent("true" | "false")):
			return macro : Bool;
		default:
		}
		return null;
	}


	static var hasRetVal : Bool;
	static function hasReturnVal( e : Expr ) {
		hasRetVal = false;
		checkRetVal(e);
		return hasRetVal;
	}

	static function checkRetVal( e : Expr ) {
		if( hasRetVal )
			return;
		switch( e.expr ) {
		case EReturn(e):
			if( e != null )
				hasRetVal = true;
		case EFunction(_):
			return;
		default:
			haxe.macro.ExprTools.iter(e, checkRetVal);
		}
	}

	static function superImpl( name : String, e : Expr ) {
		switch( e.expr ) {
		case EField( esup = { expr : EConst(CIdent("super")) }, fname) if( fname == name ):
			e.expr = EField(esup, name+"__impl");
		default:
		}
		return haxe.macro.ExprTools.map(e, superImpl.bind(name));
	}

	static function replaceSetter( fname : String, setExpr : Expr -> Expr, e : Expr ) {
		switch( e.expr ) {
		case EBinop(OpAssign, e1 = { expr : (EConst(CIdent(name)) | EField( { expr : EConst(CIdent("this")) }, name)) }, e2) if( name == fname ):
			e.expr = EBinop(OpAssign,e1,setExpr(e2));
		case EBinop(OpAssignOp(_), { expr : (EConst(CIdent(name)) | EField( { expr : EConst(CIdent("this")) }, name)) }, _) if( name == fname ):
			throw "TODO";
		default:
			haxe.macro.ExprTools.iter(e, function(e) replaceSetter(fname,setExpr,e));
		}
	}

	public static function buildSerializer() {
		var fields = Context.getBuildFields();
		var pos = Context.currentPos();
		var noCompletion = [{ name : ":noCompletion", pos : pos }];

		fields.push({
			name : "initCLIDS",
			pos : pos,
			access : [AStatic, APrivate],
			meta : noCompletion,
			kind : FFun({ args : [], ret : null , expr : macro {
				var serializables = CompileTime.getAllClasses(Serializable);
				for( cl in serializables ) {
					var fl : Dynamic = Reflect.field(cl, "initCLID");
					Reflect.callMethod(cl, fl, []);
				}
			} }),
		});

		return fields;
	}

	#end

}
