use
    alba.base.endorelation
    lambda_basic
    lambda_substitution
end

{:
Missing Theorems from Module 'endorelation'
===========================================
:}

A:ANY

{:
Missing Theorems from Module 'lambda_basic'
===========================================
:}



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


all(a,b:TERM)
        -- Parallel beta reduction is a subset of '*beta'
    require
        beta2(a,b)
    ensure
        (*beta)(a,b)
    inspect
        beta2(a,b)
    case all(a,b,c,d) beta2(a,b) ==> beta2(c,d) ==> beta2(a * c,b * d)
        assert
            (*beta)(a*c,b*c)    -- ind hypo 1
            (*beta)(b*c,b*d)    -- ind hypo 2
            (*beta)(a*c,b*d)    -- transitivity of '*beta'
    case all(a,b,c,d) beta2(a,b) ==> beta2(c,d) ==> beta2(lam(a) * c,b.sub(d))
        assert
            (*beta)(lam(a)*c, lam(b)*c)
            (*beta)(lam(a)*c, lam(b)*d)
    end


all(a,b:TERM, n,m:NATURAL)
        -- Parallel beta reducibles can be shifted up.
    require
         beta2(a,b)
    ensure
         beta2(a.up_from(n,m), b.up_from(n,m))
    inspect
         beta2(a,b)
    case all(a,b,c,d) beta2(a,b) ==> beta2(c,d) ==> beta2(lam(a) * c,b.sub(d))
        -- goal: beta2((lam(a) * c).up_from(n),b.sub(d).up_from(n))
        assert
            beta2(a.up_from(n+1,m),b.up_from(n+1,m))     -- ind hypo1
            beta2(c.up_from(n,m),d.up_from(n,m))         -- ind hypo2
            beta2(lam(a.up_from(n+1,m)) * c.up_from(n,m)
                 , b.up_from(n+1,m).sub(d.up_from(n,m))) -- def beta2

            (lam(a) * c).up_from(n,m)
            = lam(a.up_from(n+1,m)) * c.up_from(n,m)  -- def 'up_from'

            b.sub(0,d).up_from(n,m)
            = b.up_from(n+1,m).sub(0,d.up_from(n,m))
                           -- Lemma: Swap substitution an upshifting

            ( lam(a.up_from(n+1,m)) * c.up_from(n,m)
            , b.up_from(n+1,m).sub(d.up_from(n,m))
            )
            =
            ( (lam(a) * c).up_from(n,m)
            , b.sub(d).up_from(n,m)
            )
    end



all(a,b:TERM)
        -- Parallel beta reducibles can be shifted up.
    require
         beta2(a,b)
    ensure
         beta2(a.up, b.up)
    assert
         beta2(a.up_from(0,1), b.up_from(0,1))
    end





all(a,b,c,d:TERM, n:NATURAL)
    {: (Parallel) beta reducibles can be substituted by beta reducibles. :}
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
        )
    case all(u,x,v,y) beta2(u,x) ==> beta2(v,y) ==>
                          beta2(lam(u) * v, x.sub(y))
        {: goal: beta2( (lam(u)*v).sub(n,c), x.sub(y).sub(n,d) )
        :}
        assert
            -- The two specialized induction hypotheses for (u,x) and (v,y)
            beta2( u.sub(n+1,c.up), x.sub(n+1,d.up) )
            beta2( v.sub(n,c), y.sub(n,d) )

            -- Evaluate the left part of the goal
            (lam(u)*v).sub(n,c) = lam(u.sub(n+1,c.up)) * v.sub(n,c)


            -- The evaluated left part is a redex which under the premises
            beta2(c.up, d.up)
            beta2(u, x)
            beta2(v, y)
            beta2(u.sub(n+1,c.up), x.sub(n+1,d.up))

            -- can by definition of 'beta2' be reduced by
            beta2( lam(u.sub(n+1,c.up)) * v.sub(n,c),
                   x.sub(n+1,d.up).sub(y.sub(n,d)) )

            -- The right part of the latter is equal to the right part of the goal
            x.sub(n+1,d.up).sub(y.sub(n,d)) = x.sub(y).sub(n,d)

            -- Therefore the following equality proves the goal
            ( lam(u.sub(n+1,c.up)) * v.sub(n,c)
            , x.sub(n+1,d.up).sub(y.sub(n,d))
            )
            =
            ( (lam(u)*v).sub(n,c)
            , x.sub(y).sub(n,d)
            )
    end



all(a,c:TERM)
    require
        beta2(lam(a),c)
    ensure
        some(d) c = lam(d)
    inspect
        beta2(lam(a),c)
    case all(b,c) beta2(b,c) ==> beta2(lam(b),lam(c))
        assert
            lam(c) = lam(c)
    end





all(a,b:TERM)
    require
        beta2(lam(a),lam(b))
    ensure
        beta2(a,b)
    inspect
        beta2(lam(a),lam(b))
    case all(x) beta2(x,x)
        assert
            lam(a) = lam(b)
            a = b
    case all(x,y) beta2(x,y) ==> beta2(lam(x),lam(y))
        assert
           true
           a = x
           b = y
           (x,y) = (a,b)
    end







{: Probably not needed
all(a,b,c,d:TERM)
    require
        beta2(lam(a)*b, lam(c)*d)
    ensure
        beta2(a,c) and beta2(b,d)
    assert
       lam(a)*b = lam(a)*b
       lam(c)*d = lam(c)*d

       all(x,y)
           require
               lam(a)*b = x
               lam(c)*d = y
               beta2(x,y)
           ensure
                beta2(a,c) and beta2(b,d)
           inspect
               beta2(x,y)
           case all(z) beta2(z,z)
               assert
                   a = c
                   b = d
           case all(q,r,s,t) beta2(q,r) ==> beta2(s,t) ==>
                             beta2(lam(q)*s, r.sub(t))
               -- goal: beta2(a,c) and beta2(b,d)
               assert
                   lam(a) = lam(q)
                   b = s
                   a = q

           end
    end
:}



all(a,b,c:TERM)
    require
        beta2(a,b)
        beta2(a,c)
    ensure
        some(d) beta2(b,d) and beta2(c,d)
    inspect
        beta2(a,b)
    case all(x) beta2(x,x)
        assert
            beta2(x,c) and beta2(c,c)
    case all(a,b) beta2(a,b) ==> beta2(lam(a),lam(b))
        {: goal: some(f:TERM) beta2(lam(b),f) and beta2(c,f)

           a -> d        d exists because beta2(lam(a),c)
           |    |
           v    v
           b -> e        e exists because of the induction hypothesis

           lam(a) -> lam(d)   lam(d) = c
           |         |
           v         v
           lam(b) -> lam(e)
        :}
        -- beta2(lam(a), c) is in the assumptions, therefore we have
        -- (see lemma above)
        via some(d) c = lam(d)
        assert
            -- which results in
            beta2(a,d)
        -- from the induction hypothesis we get some e
        via some(e) beta2(b,e) and beta2(d,e)
        assert
            -- now we complete the diamond on the lambdas
            beta2(lam(b),lam(e)) and beta2(c,lam(e))
    case all(u,v,x,y) beta2(u,v) ==> beta2(x,y) ==> beta2(u*x,v*y)
        {: goal: some(d:TERM) beta2(v * y,d) and beta2(c,d)
        :}
        (inspect
             beta2(u*x,c)
         case all(c) beta2(c,c)
             assert
                  beta2(v*y,v*y) and beta2(c,v*y)
         case all(q,r,s,t) beta2(q,r) ==> beta2(s,t) ==>
                           beta2(q*s, r*t)
             {: u=q  ->  r           x=s -> t
                |        |           |      |
                v        v           v      v
                v    ->  d           y   -> e

                d and e exist by the outer induction hypotheses

                u*x  ->  r*t
                |        |
                v        v
                v*y  ->  d*e
             :}
             assert
                 u = q; x = s; beta2(u,r); beta2(x,t)
             via some(d) beta2(v,d) and beta2(r,d)
             via some(e) beta2(y,e) and beta2(t,e)
             assert
                 beta2(v*y,d*e) and beta2(r*t,d*e)
         case all(q,r,s,t) beta2(q,r) ==> beta2(s,t) ==>
                           beta2(lam(q)*s, r.sub(t))
             -- goal: some(d:TERM) beta2(v*y,d) and beta2(r.sub(t),d)
             assert
                 u = lam(q)
                 x = s
                 some(o) v = lam(o)
                 beta2(u,lam(r))
             {:  u=lam(q)  -> lam(r)         x  ->  t
                 |            |              |      |
                 v            v              v      v
                 v=lam(o)  -> e              y  ->  g

                 e exists by the outer induction hypothesis and it must
                   have the form lam(f)

                 g exists by the outer induction hypothesis

                 From the left diamond we infer

                 q  ->  r
                 |      |
                 v      v
                 o  ->  f

                 We get
                     lam(o),y -> f.sub(g)
                     r.sub(t) -> f.sub(g)
             :}
             via some(o) v = lam(o)
             via some(e) beta2(v,e) and beta2(lam(r),e)
             via some(f) e = lam(f)
             via some(g) beta2(y,g) and beta2(t,g)
                 assert
                     beta2(v,e)
                     beta2(lam(o),lam(f))
                     beta2(lam(o)*y, f.sub(g))
                     beta2(v*y, f.sub(g)) and beta2(r.sub(t), f.sub(g))
        )
    case all(u,v,x,y) beta2(u,v) ==> beta2(x,y) ==> beta2(lam(u)*x,v.sub(y))
        {: goal: some(d:TERM) beta2(v.sub(y),d) and beta2(c,d)
           hypo: all(c:TERM) beta2(u,v) ==> beta2(u,c) ==>
                              (some(d:TERM) beta2(v,d) and beta2(c,d))
                 all(c:TERM) beta2(x,y) ==> beta2(x,c) ==>
                              (some(d:TERM) beta2(y,d) and beta2(c,d))

        :}
        (inspect
             beta2(lam(u)*x,c)
         case all(c) beta2(c,c)
             assert
                 beta2(v.sub(y),v.sub(y)) and beta2(c,v.sub(y))
         case all(q,r,s,t) beta2(q,r) ==> beta2(s,t) ==>
                           beta2(lam(q)*s, r.sub(t))
             {: goal: some(d:TERM) beta2(v.sub(y),d) and beta2(r.sub(t),d)

                u=q  ->  r           x=s -> t
                |        |           |      |
                v        v           v      v
                v    ->  d           y   -> e

                d and e exist by the outer induction hypotheses

                lam(u)*x  ->  r.sub(t)
                |             |
                v             v
                v.sub(y)  ->  d.sub(e)
             :}
             assert
                 u=q; x=s;  beta2(u,r); beta2(x,t)
             via some(d) beta2(v,d) and beta2(r,d)
             via some(e) beta2(y,e) and beta2(t,e)
                 assert
                     beta2(v.sub(y),d.sub(e)) and beta2(r.sub(t),d.sub(e))
         case all(q,r,s,t) beta2(q,r) ==> beta2(s,t) ==> beta2(q*s,r*t)
             {:
                 q = lam(u), x = s, q->r, therefore some(o) r = lam(o)

                 because q->r we get u->o

                 u -> o          x=s -> t
                 |    |          |      |
                 v    v          v      v
                 v -> d          y   -> e

                 d and e exist by outer induction hypotheses
             :}
             assert
                 q = lam(u)
                 x = s
                 beta2(q,lam(v))
             via some(o) r = lam(o)
             via some(d) beta2(v,d) and beta2(o,d)
             via some(e) beta2(y,e) and beta2(t,e)
             assert
                 beta2(v.sub(y), d.sub(e)) and beta2(r*t, d.sub(e))
        )
    end
