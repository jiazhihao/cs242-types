var _ = require('underscore');

var Expr   = require('./expr');
var Decl   = require('./decl');
var Type   = require('./type');
var Pat    = require('./pat');

var Ctx    = require('./ctx').Ctx;
var MutCtx = require('./ctx').MutCtx;


// Generate the type of the pattern, updating the set of constraints
// and context accordingly.
// @param {[TypeConstraint]}    eq, set of constraints
// @param {MutCtx}              m_ctx, mutable typing context
// @returns {Type}              type of the pattern
Pat.prototype.typeOf = function(eq, m_ctx) {
  if (this.isVar) {
    if (m_ctx.binds(this.name)) {
      throw new Error("Variable '" + this.name + "' already bound");
    }
    // Generate fresh type variable and add it to the context
    var t = fresh();
    m_ctx.add(this.name, t);
    return t;
  }
  // <Task2>
  if (this.isPair){
    return Type.Pair(this.fst.typeOf(eq, m_ctx), this.snd.typeOf(eq, m_ctx));
  }
  
  if (this.isCons){
    var headType = this.head.typeOf(eq, m_ctx)
    eq.push([Type.List(headType), this.tail.typeOf(eq, m_ctx)])
    return Type.List(headType);
  }
  
  if (this.isNil){
    return Type.List(fresh());
  }
  // </Task2>
  throw new Error("Woops, I found a bug.");
}

// Generate the type of the expression, updating the set of contraints
// as necessary.
// @param {[TypeConstraint]} eq
// @param {Ctx}              ctx, immutable typing context
// @returns {Type}           type of expression
Expr.prototype.typeOf = function(eq, ctx) {
  if (this.isVar) {
    if (!ctx.binds(this.name)) {
      throw new Error("Unbound variable '" + this.name + "'");
    }
    return ctx.get(this.name);
  }
  // <Task1>
  if (this.isInt) {
    return Type.Int;
  }
  
  if (this.isBool) {
    return Type.Bool;
  }

  if (this.isIf) {
    var condTy = this.cond.typeOf(eq, ctx);
    var thenTy = this.then.typeOf(eq, ctx);
    var elseTy = this.else_.typeOf(eq, ctx);
    eq.push([condTy, Type.Bool]);
    eq.push([thenTy, elseTy]);
    return thenTy;
  }

  if (this.isNil) {
    return Type.List();
  }

  if (this.isLambda) {
    var nameTy = fresh();
    var bodyTy = this.body.typeOf(eq, ctx.add(this.name, nameTy));
    return Type.Arrow(nameTy, bodyTy);
  }

  if (this.isApp) {
    var argTy = this.arg.typeOf(eq, ctx);
    var funTy = this.fun.typeOf(eq, ctx);
    eq.push([funTy.from, argTy]);
    return funTy.to;
  }

  if (this.isPair) {
    fstTy = this.fst.typeOf(eq, ctx);
    sndTy = this.snd.typeOf(eq, ctx);
    return Type.Pair(fstTy, sndTy);
  }
  // </Task1>
  throw new Error("Woops, I found a bug.");
}

// Export typeOf methods
exports.typeOf = { pat : Pat.prototype.typeOf
                 , expr : Expr.prototype.typeOf
                 , decl : Decl.prototype.typeOf };

// Global typing context containing some pre-defined symbols
var globalCtx = 
  Ctx().add("+",  Type.Arrow(Type.Int, Type.Arrow(Type.Int, Type.Int)))
       .add("==", Type.Arrow(Type.Int, Type.Arrow(Type.Int, Type.Bool)));

// Generate the type of the declaration adn update the set of
// constraints.
// @param {[TypeConstraint]}    eq, set of constraints
Decl.prototype.typeOf = function(eq) {
  // Generate fresh type variable for this declaration
  var t = fresh();
  // Create the typing context containg this declaration and all
  // globals. This context is mutable since we may introduce new
  // variables in the patterns that should be used when typing the
  // body.
  var m_ctx = MutCtx(globalCtx).add(this.name, t);

  // Get the type of the pattern, mutating the constraints and contex
  // as necessary
  var t_pat = this.pat.typeOf(eq, m_ctx);

  // Create an immutable context from m_ctx and type the body of the
  // declaration under this context, updating the constraints as
  // necessary
  var t_body = this.body.typeOf(eq, Ctx(m_ctx));
  // Add constraint that the type variable of the declaration is an
  // arrow type: type of pattern -> type of body
  eq.push([t, Type.Arrow(t_pat, t_body)]);

  return t;
}

var freshCtr = 0;
// Generate fresh type variables
function fresh() {
  return Type.Var("_t" + freshCtr++);
}

// Compute the constraint typing rule for top-level declarations.
// That is, given a program (list of declarations), this function
// returns the type and set of constraints.
//
// @param {[Decl]}     decls, list of declarations
// @returns {type: Type, constraint: [[Type, Type]]} type of
// definition and set of constraints
function constraintTypeOf(decls) {
  var toplevel;
  // Create empty array of equations/constraints
  var eq = [];
  _.each(decls, function (decl) {
    // Get type of declaration, update constraints
    var t_d = decl.typeOf(eq);

    if (!toplevel) {
      // This is the first declaration, remember it
      toplevel = { name: decl.name, type: t_d };
    } else if (decl.name === toplevel.name) {
      // All other declarations have same type as the first
      eq.push([toplevel.type, t_d])
    } else {
      // Only one definition (though multiple declarations) supported
      throw new Error("Multiple definitions not supported");
    }
  });
  return { type: toplevel.type, constraints: eq };
}

// Return the contraints of a program
module.exports.constraintsOf = function(decls) {
  return constraintTypeOf(decls).constraints;
};

// Solve type constraints.
// @param {[TypeConstraint]}    todo, list of type constraints
// @returns {Ctx}               substituion mapping names to types
//
// A TypeConstraint is an array of two Types [t1, t2] denoting
// equality between t1 and t2.

function rename(type, oldname, newtype){ // strips vars named oldname, adds in newtype
    if(type.isVar && type.name == oldname)
        return newtype;
    if(type.isVar && type.name != oldname)
        return type;
    if(type.isArrow)
        return Type.Arrow(rename(type.from, oldname, newtype), rename(type.to, oldname, newtype));
    if(type.isInt)
        return Type.Int;
    if(type.isBool)
        return Type.Bool;
    if(type.isList)
        return Type.List(rename(type.elem, oldname, newtype));
    if(type.isPair)
        return Type.Pair(rename(type.fst, oldname, newtype), rename(type.snd, oldname, newtype));
}

function solveConstraints(todo) {
  // <Task4>
  var solved = [];
  var c;
  while (c = todo.pop()) {
    var lhs = c[0];
    var rhs = c[1];
    if (lhs.isVar || rhs.isVar) {
        var oldname;
        var newtype;
        if(lhs.isVar){
            oldname = lhs.name;
            newtype = rhs;
        }
        else{
            oldname = rhs.name;
            newtype = lhs;
        }
        for (var i = 0; i < solved.length; i++) {
            solved[i][1] = rename(solved[i][1], oldname, newtype);
        }
        solved.push([oldname, newtype]);

        var todo2 = [];
        var c2;
        while(c2 = todo.pop()){
            todo2.push([rename(c2[0], oldname, newtype), rename(c2[1], oldname, newtype)]);
        }
        todo = todo2;
    }
    else if (lhs.isArrow) {
        if (!rhs.isArrow)
            throw new UnificationError(c);
        else {
            todo.push([lhs.from, rhs.from]);
            todo.push([lhs.to, rhs.to]);
        }
    }
    else if (lhs.isInt) {
        if (!rhs.isInt){
            throw new UnificationError(c);
        }
    }
    
    else if (lhs.isBool) {
        if (!rhs.isBool){
            throw new UnificationError(c);
        }
    }
    
    else if (lhs.isList) {
        if (!rhs.isList){
            throw new UnificationError(c);
        }
        else
            todo.push([lhs.elem, rhs.elem]);
    }
    
    else if (lhs.isPair) {
        if (!rhs.isPair)
            throw new UnificationError(c);
        else {
            todo.push([lhs.fst, rhs.fst]);
            todo.push([lhs.snd, rhs.snd]);
        }
    }
  }
  return Ctx(_.map(solved, function (constraint) {
    return {name: constraint[0], type: constraint[1]};
  }));
  // </Task4>
}
module.exports.solveConstraints = solveConstraints;

// Encoding unification error
function UnificationError(c) {
  var e = new Error();
  e.name    = 'UnificationError';
  e.message = "Could not unify '" + c[0].pretty() + 
                 "' with '" + c[1].pretty() + "'";
  return e;
}

// Perform an occurs check. Does the name occur in this type?
// @param {String}    name
// @returns {Bool}    true if name occurs in this type, false otherwise
Type.prototype.occurs = function(name) {
  // <Task3>
  if(this.isVar)
    return name == this.name;
  if(this.isArrow)
    return this.from.occurs(name) || this.to.occurs(name);
  if(this.isInt)
    return false;
  if(this.isBool)
    return false;
  if(this.isList)
    return this.elem.occurs(name);
  if(this.isPair)
    return this.fst.occurs(name) || this.snd.occurs(name);
  // </Task3>
}
exports.occurs = Type.prototype.occurs;

// Infer type of program by computing the set of type constraints and
// solving them.
//
// @param {[Decl]}     decls, list of program declarations
// @returns {Type}     inferred type
function inferTypes(decls) {
  var tr  = constraintTypeOf(decls);

  // <Task0>
  for (var i = 0; i < tr.constraints.length; i++) {
    console.log(tr.constraints[i].pretty());
  }

  console.log("function has (unsolved) type: " + tr.type.pretty());
  // </Task0>

  var ctx = solveConstraints(tr.constraints);
  return tr.type.multiSubst(ctx);
}
module.exports.inferTypes = inferTypes;
