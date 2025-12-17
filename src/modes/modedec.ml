ModeDec   MODEDEC  struct (*! structure ModeSyn = ModeSyn' !*)
(*! structure Paths = Paths' !*)
exception module module module type Arg(* Representation invariant:

       The modes of parameters are represented in the following mode list

       M ::= . | M, <Marg, Arg>

       G corresponds to a context. We say M is a mode list for U, if
       G |- U : V and M assigns modes to parameters in G
         (and similarly for all other syntactic categories)

       The main function of this module is to
        (a) assign modes to implicit arguments in a type family
        (b) check the mode specification for consistency

       Example:

         a : type.
         b : a -> a -> type.
         c : b X X -> b X Y -> type.

       Then

         %mode c +M -N.

       will infer X to be input and Y to be output

         %mode +{X:a} -{Y:a} +{M:b X Y} -{N:b X Y} (c M N).

       Generally, it is inconsistent
       for an unspecified ( * ) or output (-) argument to occur
       in the type of an input (+) argument
    *)
let rec error(r,  , msg) raise (error (wrap (r,  , msg)))(* checkname mS = ()

       Invariant:
       mS modeSpine, all modes are named.
       If mS contains two entries with the same name
       then Error is raised
    *)
let rec checkName(mnil) () checkName(mapp (marg (_,  , sOME name),  , mS)) let let rec checkName'(mnil) () checkName'(mapp (marg (_,  , sOME name'),  , mS)) if name = name' then raise (error ("Variable name clash: " ^ name ^ " is not unique")) else checkName' mS in checkName' mS(* modeConsistent (m1, m2) = true
       iff it is consistent for a variable x with mode m1
           to occur as an index object in the type of a variable y:V(x) with mode m2

       m1\m2 + * - -1
        +    Y Y Y Y
        *    N y n n
        -    N y Y n
        -1   N Y Y Y

       The entries y,n constitute a bug fix, Wed Aug 20 11:50:27 2003 -fp
       The entry n specifies that the type
    *)
let rec modeConsistent(star,  , plus) false modeConsistent(star,  , minus) false modeConsistent(star,  , minus1) false modeConsistent(minus,  , plus) false modeConsistent(minus,  , minus1) false modeConsistent(minus1,  , plus) false modeConsistent_ true(* empty (k, ms, V) = (ms', V')

       Invariant:
       If    V = {A_1} .. {A_n} V1   in Sigma
       and   V has k implicit arguments
       then  ms' = ms, <( *, NONE), Implicit>  ... <( *, NONE), Implicit>   (k times)
       and   V' = V1
    *)
let rec empty(0,  , ms,  , v) (ms,  , v) empty(k,  , ms,  , pi (_,  , v)) empty (k - 1,  , decl (ms,  , (marg (star,  , nONE),  , implicit)),  , v)(* inferVar (ms, m, k) = ms'

       Invariant:
       If  ms is a mode list,
       and k is declared with mode mk in ms
       and m is the mode for a variable y in whose type k occurs
       then ms' is the same as ms replacing only mk by
       mk' = m o mk

        m o mk  + * - -1
        ----------------
        +       + + + +
        *       + * - -1
        -       + - - -1
        -1      + -1-1-1

        Effect: if the mode mk for k was explicitly declared and inconsistent
                with m o mk, an error is raised
    *)
let rec inferVar(decl (ms,  , (marg (star,  , nameOpt),  , implicit)),  , mode,  , 1) decl (ms,  , (marg (mode,  , nameOpt),  , implicit)) inferVar(decl (ms,  , (marg (_,  , nameOpt),  , implicit)),  , plus,  , 1) decl (ms,  , (marg (plus,  , nameOpt),  , implicit)) inferVar(decl (ms,  , (marg (minus,  , nameOpt),  , implicit)),  , minus1,  , 1) decl (ms,  , (marg (minus1,  , nameOpt),  , implicit)) inferVar(ms as decl (_,  , (_,  , implicit)),  , _,  , 1) ms inferVar(ms as decl (_,  , (_,  , local)),  , _,  , 1) ms inferVar(ms as decl (_,  , (marg (mode',  , sOME name),  , explicit)),  , mode,  , 1) if modeConsistent (mode',  , mode) then ms else raise (error ("Mode declaration for " ^ name ^ " expected to be " ^ modeToString mode)) inferVar(decl (ms,  , md),  , mode,  , k) decl (inferVar (ms,  , mode,  , k - 1),  , md)(* inferExp (ms, m, U) = ms'

       Invariant:
       If  ms is a mode list for U,   (U in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in U,
         wrt. to m. (see inferVar)
    *)
let rec inferExp(ms,  , mode,  , root (bVar (k),  , s)) inferSpine (inferVar (ms,  , mode,  , k),  , mode,  , s) inferExp(ms,  , mode,  , root (const (cid),  , s)) inferSpine (ms,  , mode,  , s) inferExp(ms,  , mode,  , root (def (cid),  , s)) inferSpine (ms,  , mode,  , s) inferExp(ms,  , mode,  , root (fgnConst (cs,  , conDec),  , s)) inferSpine (ms,  , mode,  , s) inferExp(ms,  , mode,  , lam (d as dec (nameOpt,  , _),  , u)) ctxPop (inferExp (decl (inferDec (ms,  , mode,  , d),  , (marg (mode,  , nameOpt),  , local)),  , mode,  , u)) inferExp(ms,  , mode,  , pi ((d as dec (nameOpt,  , _),  , _),  , v)) ctxPop (inferExp (decl (inferDec (ms,  , mode,  , d),  , (marg (mode,  , nameOpt),  , local)),  , mode,  , v)) inferExp(ms,  , mode,  , fgnExp _) ms(* inferSpine (ms, m, S) = ms'

       Invariant:
       If  ms is a mode list for S,   (S in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in S,
         wrt. to m. (see inferVar)
    *)
 inferSpine(ms,  , mode,  , nil) ms inferSpine(ms,  , mode,  , app (u,  , s)) inferSpine (inferExp (ms,  , mode,  , u),  , mode,  , s)(* inferDec (ms, m, x:V) = ms'

       Invariant:
       If  ms is a mode list for V,   (V in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in V,
         wrt. to m.   (see inferVar)
    *)
 inferDec(ms,  , mode,  , dec (_,  , v)) inferExp (ms,  , mode,  , v)(* inferMode ((ms, V), mS) = ms'

       Invariant:
       If  ms is a mode list for V,
       and mS is a mode spine,
       then ms' is the mode list for V which is consistent with V.
    *)
let rec inferMode((ms,  , uni (type)),  , mnil) ms inferMode((_,  , uni (type)),  , _) raise (error "Too many modes specified") inferMode((ms,  , pi ((dec (name,  , v1),  , _),  , v2)),  , mapp (marg (mode,  , _),  , mS)) ctxPop (inferMode ((decl (inferExp (ms,  , mode,  , v1),  , (marg (mode,  , name),  , explicit)),  , v2),  , mS)) inferMode((ms,  , root _),  , _) raise (error "Expected type family, found object constant") inferMode_ raise (error "Not enough modes specified")(* abstractMode (ms, mS) = mS'

       Invariant:
       If    V = {A1} .. {An} V1  is a type (with n implicit parameter)
       and   ms is a mode list for V,
       then  mS' = {m1} .. {mn} mS
       where m1 .. mn are the infered modes for the implicit parameters
    *)
let rec abstractMode(ms,  , mS) let let rec abstractMode'(null,  , mS,  , _) mS abstractMode'(decl (ms,  , (marg,  , _)),  , mS,  , k) abstractMode' (ms,  , mapp (marg,  , mS),  , k + 1) in abstractMode' (ms,  , mS,  , 1)(* shortToFull (cid, mS, r) = mS'

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is a mode spine in short form (implicit parameters are not moded),
       then mS' is a mode spine in full form (all parameters are moded)

       Full form can be different then intended by the user.
    *)
let rec shortToFull(a,  , mS,  , r) let let rec calcImplicit'(conDec (_,  , _,  , k,  , _,  , v,  , _)) abstractMode (inferMode (empty (k,  , null,  , v),  , mS),  , mS) calcImplicit'(conDef (_,  , _,  , k,  , _,  , v,  , _,  , _)) abstractMode (inferMode (empty (k,  , null,  , v),  , mS),  , mS) in try  with (* re-raise Error with location *)
(* checkFull (a, mS, r) = ()

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is not a valid mode spine in full form then
       exception Error is raised.
    *)
let rec checkFull(a,  , mS,  , r) try  with (* re-raise error with location *)
(* checkPure (a, mS, r) = ()
       Effect: raises Error(msg) if the modes in mS mention (-1)
    *)
let rec checkPure((a,  , mnil),  , r) () checkPure((a,  , mapp (marg (minus1,  , _),  , mS)),  , r) error (r,  , "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')") checkPure((a,  , mapp (_,  , mS)),  , r) checkPure ((a,  , mS),  , r)let  inlet  inlet  inend