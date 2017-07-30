use
    alba.base.natural
    alba.base.endorelation
end

{:
Theorems of NATURAL
===================
:}
all(i,j:NATURAL)
    require
        i < j
        j <= i
    ensure
        false
    end

{:
Theorems of 'endorelation'
==========================
:}

A: ANY

all(r:{A,A}, a,b:A)
    require
        r(a,b)
    ensure
        (*r)(a,b)
    assert
        (*r)(a,a)
    end


class
    TERM
create
    var(id:NATURAL)
    (*) (fun,arg:TERM)
    lam (inner:TERM)
end





{: Shifting terms up
   =================
:}
up_from (t:TERM, start,n:NATURAL): TERM
        -- The term 't' with all variables from 'start' shifted up by 'n'.
    -> inspect
           t
       case var(i) then
           if i < start then
               var(i)
           else
               var(i+n)
       case a * b then
           a.up_from(start,n) * b.up_from(start,n)
       case lam(a) then
           lam( a.up_from(start+1,n) )


up (t:TERM): TERM
    -> t.up_from(0,1)

up(a:TERM,k:NATURAL):TERM
    -> a.up_from(0,k)





{: Substitution of variables
   =========================
:}
sub (a:TERM, n:NATURAL, b:TERM): TERM
        -- The term 'a' with variable 'n' substituted by 'b'.
    -> inspect
           a
       case var(i) then
           if i < n then
               var(i)
           else if i = n then
               b
           else
               var(i - 1)
       case x * y then
           x.sub(n,b) * y.sub(n,b)
       case lam(x) then
           lam ( x.sub(n+1, b.up) )

sub (a,b:TERM): TERM
    -> a.sub(0,b)


all(a:TERM, i:NATURAL)
    ensure
        var(i).sub(i,a) = a
    if i < i
    else if i = 0
    else
    end

all(a:TERM,i,j:NATURAL)
    require
        i < j
    ensure
        var(i).sub(j,a) = var(i)
    if i < j
    else if i = j
    else
    end


all(a:TERM,i,j:NATURAL)
    require
        j < i
    ensure
        var(i).sub(j,a) = var(i-1)
    if i < j
    else if i = j
    else
    end

{:
all(a:TERM)
    ensure
        lam(var(0)).sub(0,a) = lam(var(0))   -- necessary??
    end


all(a:TERM)
    ensure
        lam(var(1)).sub(0,a) = lam(a.up)     -- necessary??
    end
:}

{: Beta reduction
   ==============
:}
beta: ghost {TERM,TERM}
    = {(r):
          all(a,b) r(lam(a)*b, a.sub(b))
          ,
          all(a,b) r(a,b) ==> r(lam(a), lam(b))
          ,
          all(a,b,c) r(a,b) ==> r(a*c, b*c)
          ,
          all(a,b,c) r(a,b) ==> r(c*a, c*b)
      }


all(a,b:TERM)
    ensure
        beta(lam(a)*b, a.sub(0,b))
    assert
        beta(lam(a)*b, a.sub(b))
    end

all(a:TERM)
    ensure
        a in beta.range
    assert
        var(0).sub(a) = a
        beta(lam(var(0))*a, var(0).sub(a))
    end


all(a,b:TERM)
    require
        (*beta)(a,b)
    ensure
        (*beta)(lam(a),lam(b))
    inspect
        (*beta)(a,b)
    end

all(a,b,c:TERM)
    require
         (*beta)(a,b)
    ensure
         (*beta)(a*c,b*c)
    inspect
         (*beta)(a,b)
    case all(x,y,z) (*beta)(x,y) ==> beta(y,z) ==> (*beta)(x,z)
    {:  ind hypo:  all(c:TERM) (* beta)(x,y) ==> (* beta)(x * c,y * c)
    :}
        assert
           (*beta)(x*c,y*c)  -- ind hypo (Why not yet specialized???)
                             -- 'c' does not occur in the preconditions!!!!
           beta(y*c,z*c)
    end


all(a,b,c:TERM)
    require
         (*beta)(a,b)
    ensure
         (*beta)(c*a,c*b)
    inspect
         (*beta)(a,b)
    case all(x,y,z) (*beta)(x,y) ==> beta(y,z) ==> (*beta)(x,z)
    {:  ind hypo: all(c:TERM) (* beta)(x,y) ==> (* beta)(c * x,c * y) :}
        assert
            (* beta)(c * x,c * y)
           beta(c*y,c*z)
    end




{:
Reducible and Normal Terms
==========================
:}

is_reducible (a:TERM): ghost BOOLEAN
    -> a in beta.domain

is_normal (a:TERM): ghost BOOLEAN
    -> not a.is_reducible


all(a:TERM)
    require
        not a.is_normal
    ensure
        a.is_reducible
    via require
        not a.is_reducible
    end

all(a:TERM)
    require
        not a.is_normal
    ensure
        some(b) beta(a,b)
    assert
        a.is_reducible
    end


all(a:TERM)
    require
        lam(a).is_normal
    ensure
        a.is_normal
    via require
        not a.is_normal
    via some(b)
        beta(a,b)
    assert
        beta(lam(a), lam(b))
    end



{:
Beta Reduction of Some Specific Terms
=====================================
:}

all(a,c:TERM)
    require
        beta(lam(a), c)
    ensure
        some(b) beta(a,b) and c = lam(b)
    assert
        lam(a) = lam(a)
        all(x)
            require
                x = lam(a)
            ensure
                some(b) beta(a,b) and c = lam(b)
            inspect
                beta(x,c)
            case all(x,y) beta(x,y) ==> beta(lam(x),lam(y))
                assert
                    a = x
                    beta(a,y) and lam(y) = lam(y)
            end
    end



all(a:TERM)
    require
        a.is_normal
    ensure
        lam(a).is_normal
    via require
        not lam(a).is_normal
    via some(b)
        beta(lam(a),b)
    via some(x)
        beta(a,x) and b = lam(x)
    assert
        a.is_reducible
    end



all(i:NATURAL, b:TERM)
    require
        beta(var(i),b)
    ensure
        false
    assert
        all(a)
            require
                a = var(i)
            ensure
                false
            inspect
                beta(a,b)
            end
         var(i) = var(i)
    end


all(x,y,c:TERM)
     require
         beta(x*y, c)
         x.is_normal
     ensure
        x as lam(_) or y.is_reducible
    assert
        all(a)
            require
                a = x * y
            ensure
                x as lam(_) or y.is_reducible
            inspect
                beta(a,c)
            end

        x * y = x * y
    end


all(x,y,c:TERM)
     require
         beta(x*y, c)
         x.is_normal
         not (x as lam(_))
     ensure
         y.is_reducible
     assert
        x as lam(_) or y.is_reducible
     end


{:
Special Lambda Terms
====================
:}


identity: TERM
    = lam(var(0))


all(a:TERM)
    ensure
        beta(identity * a, a)
    assert
        var(0).sub(a) = a
        beta(identity * a, var(0).sub(a))
    end


true: TERM
    = lam(lam(var(1)))

false: TERM
    = lam(lam(var(0)))



all(a,b:TERM)
    ensure
        (*beta)(false * a * b, b)
    assert
        beta(lam(lam(var(0)))*a, lam(var(0)).sub(a))  -- def 'beta'

        (*beta)(false * a * b, identity * b)
        beta(identity * b, b)
    end