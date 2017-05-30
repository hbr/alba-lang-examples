use
    alba.base.natural
    alba.base.endorelation
end

all(n,i:NATURAL)
    require
        n < i
    ensure
        1 <= i
    inspect
        i
    end

all(n,m:NATURAL)
    require
        m <= n
    ensure
        n - m + m = n
    inspect
        m
    case l.successor
        inspect
            n
        case k.successor
        assert
            k - l + l = k
        via [ (k.successor - l.successor) + l.successor
            , (k - l + l).successor
            , k.successor
            ]
    end


all(n,k:NATURAL)
    require
        not (n < k)
        not (n = k)
    ensure
        k < n
    end

all(n,k:NATURAL)
    require
        k < n
    ensure
        1 <= n
    end

all(n,k:NATURAL)
    require
        not (n < k)
        not (n = k)
    ensure
        0 < n
    assert
        k < n
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
up_from (t:TERM, start:NATURAL): TERM
    -> inspect
           t
       case var(i) then
           if i < start then
               var(i)
           else
               var(i+1)
       case a * b then
           a.up_from(start) * b.up_from(start)
       case lam(a) then
           lam( a.up_from(start+1) )


up (t:TERM): TERM
    -> t.up_from(0)


all(k,n:NATURAL, a:TERM)
        -- Lemma: Swap 'up_from' with itself.
    require
        k <= n
    ensure
        a.up_from(n).up_from(k) = a.up_from(k).up_from(n+1)
    inspect
        a
    case var(i)
        if i < k
            -- no shift
            assert
                i < n
                i < n + 1
            via [ var(i) ]
        else if i < n
            -- shift by one
            assert
                i + 1 < n + 1
                i.successor < n.successor -- help the evaluator
            via [ var(i+1) ]
        else
            -- shift by two
            assert
                not (i < n)
                not (i < k)
                not (i + 1 < k);        not (i.successor < k)
                not (i + 1 < n + 1);    not (i.successor < n.successor)
            via [ var(i+1+1) ]
    case a * b
        assert
             a.up_from(n).up_from(k) = a.up_from(k).up_from(n + 1)
             b.up_from(n).up_from(k) = b.up_from(k).up_from(n + 1)
    case lam(a0)
        {: goal: lam(a0).up_from(n).up_from(k) = lam(a0).up_from(k).up_from(n + 1)
        :}
        assert
            a0.up_from(n+1).up_from(k+1)
            = a0.up_from(k+1).up_from(n+1+1)  -- specialized ind hypo

        via [ lam(a0.up_from(n+1).up_from(k+1))    -- def up_from
            , lam(a0.up_from(k+1).up_from(n+1+1))  -- ind hypo
            ]
    end



all(b:TERM, n:NATURAL)
        -- Lemma: Swap 'up_from' with 'up'.
    ensure
        b.up_from(n).up = b.up.up_from(n+1)
    via [ b.up_from(n).up_from(0)
        , b.up_from(0).up_from(n+1)
        ]
    end




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




all(i,k,n:NATURAL, b:TERM)
        -- Lemma: Swap 'up_from' with 'sub' for variable.
    require
        k <= n
    ensure
        var(i).up_from(n+1).sub(k,b.up_from(n)) = var(i).sub(k,b).up_from(n)
    if i < k
        {: variable i is not shifted and not substituted :}
        assert
            i < n
            i < n + 1
        via [ var(i) ]
    else if i = k
        {: variable i is not shifted, but substituted :}
        assert
            i < n + 1
        via [ b.up_from(n) ]
    else if i < n + 1
        {: variable i is not shifted, and not substituted :}
        assert
            i - 1 + 1 = i
            (i - 1 + 1) in {i: i < n + 1}
            i - 1 < n
            i - 0.successor < n
        via [ var(i-1) ]
    else
        {: variable i is shifted, but not substituted

           n + 1 <= i
         :}
        assert
            not (i+1 < k);     not (i.successor < k)
            not (i+1 = k);     not (i.successor = k)
            i - 1 + 1 = i

            not (i < k)
            not (i = k)

            n <= i - 1
            not (i - 1 < n)
            not (i - 0.successor < n)
        via [ var(i+1-1)
            , var(i)
            , var(i-1+1)
            ]
    end

all(k,n:NATURAL, a,b:TERM)
        -- Lemma: Swap 'up_from' and 'sub'.
    require
        k <= n
    ensure
        a.up_from(n+1).sub(k,b.up_from(n)) = a.sub(k,b).up_from(n)
    inspect
        a
    case a1 * a2
        assert
            a1.up_from(n + 1).sub(k,b.up_from(n)) = a1.sub(k,b).up_from(n)
            a2.up_from(n + 1).sub(k,b.up_from(n)) = a2.sub(k,b).up_from(n)
    case lam(a0)
        {: goal: lam(a0).up_from(n + 1).sub(k,b.up_from(n))
                 = lam(a0).sub(k,b).up_from(n)
           hypo: all(n,k) k <= n ==> a0.up_from(n+1).sub(k,b.up_from(n))
                                     = a0.sub(k,b).up_from(n)
        :}
        assert
           a0.up_from(n+1+1).sub(k+1,b.up.up_from(n+1))
           = a0.sub(k+1,b.up).up_from(n+1)  -- specialized ind hypo

           b.up_from(n).up = b.up.up_from(n+1)  -- can swap up

        via [ lam(a0).up_from(n+1).sub(k,b.up_from(n))
            , lam(a0.up_from(n+1+1).sub(k+1,b.up_from(n).up))   -- def up_from, sub
            , lam(a0.up_from(n+1+1).sub(k+1,b.up.up_from(n+1))) -- swap up
            , lam(a0.sub(k+1,b.up).up_from(n+1))                -- ind hypo
            , lam(a0).sub(k,b).up_from(n)                       -- def sub, up_from
            ]
    end





all(n:NATURAL, a,b:TERM)
        -- Lemma: Swap 'up_from' and 'sub' specialized.
    ensure
        a.up_from(n+1).sub(b.up_from(n)) = a.sub(b).up_from(n)
    via [ a.up_from(n+1).sub(0,b.up_from(n))
        , a.sub(0,b).up_from(n)
        ]
    end




all(i:NATURAL, x:TERM)
    require
        i = 0
    ensure
        var(i).sub(x) = x
    assert
        not (i < 0)
    end

all(i:NATURAL, x:TERM)
    require
        0 < i
    ensure
        var(i).sub(x) = var(i-1)
    assert
        not (i = 0)
        not (i < 0)
    end


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



all(a,b:TERM, n:NATURAL)
        -- Beta reducibles can be shifted up.
    require
         beta(a,b)
    ensure
         beta(a.up_from(n), b.up_from(n))
    inspect
         beta(a,b)
    case all(a0,b) beta(lam(a0)*b, a0.sub(b))
        -- goal: beta( (lam(a0)*b).up_from(n),  a0.sub(b).up_from(n) )
        assert
            beta( lam(a0.up_from(n+1)) * b.up_from(n),
                  a0.up_from(n+1).sub(b.up_from(n)))   -- def 'beta'

            (lam(a0)*b).up_from(n)
            = lam(a0.up_from(n+1)) * b.up_from(n) -- def 'up_from'

            a0.up_from(n+1).sub(b.up_from(n))
            = a0.sub(b).up_from(n) -- Lemma: Swap 'up_from' and 'sub'.

            ( lam(a0.up_from(n+1)) * b.up_from(n)
            , a0.up_from(n+1).sub(b.up_from(n))
            )
            =
            ( (lam(a0) * b).up_from(n)
            , a0.sub(b).up_from(n)
            )
    end







{: Parallel beta reduction
   =======================

In normal beta reduction 'lam(a)*c' reduces to 'a.sub(c)'. The subterms 'a'
and 'c' might contain more redexes. To reduce them the beta reduction requires
further steps.

In parallel beta reduction we allow

- any term to reduce to itself

- an application to reduce to an application where both operands can be reduced
  in parallel

- 'lam(a)*c' to reduce to 'b.sub(d)' as long as 'a' reduces to 'b' and 'c'
  reduces to 'd'. I.e. all redexes below any redex can be reduced in parallel.

:}

beta2: ghost {TERM,TERM}
    = {(r):
          all(a) r(a,a)
          ,
          all(a,b) r(a,b) ==> r(lam(a), lam(b))
          ,
          all(a,b,c,d) r(a,b) ==> r(c,d) ==> r(a*c, b*d)
          ,
          all(a,b,c,d) r(a,b) ==> r(c,d) ==> r(lam(a)*c, b.sub(d))
      }


all(a,b:TERM)
        -- Beta reduction is subset of parallel beta reduction.
    require
        beta(a,b)
    ensure
        beta2(a,b)
    inspect
        beta(a,b)
    end


all(a,b:TERM, n:NATURAL)
        -- Parallel beta reducibles can be shifted up.
    require
         beta2(a,b)
    ensure
         beta2(a.up_from(n), b.up_from(n))
    inspect
         beta2(a,b)
    case all(a,b,c,d) beta2(a,b) ==> beta2(c,d) ==> beta2(lam(a) * c,b.sub(d))
        -- goal: beta2((lam(a) * c).up_from(n),b.sub(d).up_from(n))
        assert
            beta2(a.up_from(n+1),b.up_from(n+1))     -- ind hypo1
            beta2(c.up_from(n),d.up_from(n))         -- ind hypo2
            beta2(lam(a.up_from(n+1)) * c.up_from(n)
                 , b.up_from(n+1).sub(d.up_from(n))) -- def beta2

            (lam(a) * c).up_from(n)
            = lam(a.up_from(n+1)) * c.up_from(n)  -- def 'up_from'

            b.sub(d).up_from(n)
            = b.up_from(n+1).sub(d.up_from(n)) -- Lemma: Swap 'up_from' and 'sub'.

            ( lam(a.up_from(n+1)) * c.up_from(n)
            , b.up_from(n+1).sub(d.up_from(n))
            )
            =
            ( (lam(a) * c).up_from(n)
            , b.sub(d).up_from(n)
            )
    end



all(a,b:TERM)
        -- Parallel beta reducibles can be shifted up.
    require
         beta2(a,b)
    ensure
         beta2(a.up, b.up)
    assert
         beta2(a.up_from(0), b.up_from(0))
    end




{:
all(a,b,c,d:TERM, n:NATURAL)
    require
        beta2(a,b)
        beta2(c,d)
    ensure
        beta2(a.sub(n,c), b.sub(n,d))
    inspect
        beta2(a,b)
    case all(a) beta2(a,a)
    -- goal: beta2(a.sub(n,c), a.sub(n,d))
        (inspect a
         case var(i)
             if i < n
             else if i = n
             else
         case a1 * a2
         case lam(a0)
         -- goal: beta2( lam(a0).sub(n,c), lam(a0).sub(n,d) )
             assert
                 all(n,c,d) beta2(c,d) ==> beta2(a0.sub(n,c),a0.sub(n,d))
                 beta2(c.up,d.up)
                 beta2(a0.sub(n,c),a0.sub(n,d))
                 beta2( a0.sub(n+1,c.up), a0.sub(n+1,d.up) )
                 lam(a0).sub(n,c) = lam(a0.sub(n+1,c.up))
                 lam(a0).sub(n,d) = lam(a0.sub(n+1,d.up))
        )
    case all(a1,a2,b1,b2) beta2(a1,a2) ==> beta2(b1,b2) ==>
                          beta2(lam(a1) * b1, a2.sub(b2))
    {: goal: beta2( (lam(a1)*b1).sub(n,c), a2.sub(b2).sub(n,d) )
    :}
        assert
            (lam(a1)*b1).sub(n,c) = lam(a1.sub(n+1,c.up)) * b1.sub(n,c)
            beta2( b1.sub(n,c), b2.sub(n,d) )
            beta2( a1.sub(n+1,c.up), a2.sub(n+1,d.up) )

            beta2( lam(a1.sub(n+1,c.up)) * b1.sub(n,c),
                   a2.sub(n+1,d.up).sub(b2.sub(n,d)) )   -- def 'beta2'

            {: Missing: Swapping of substitutions!!!
               for all k <= n
               a.sub(k,b).sub(n,c) = a.sub(n+1,c.up).sub(k,b)
            :}
    end
:}
