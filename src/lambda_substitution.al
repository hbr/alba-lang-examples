use
   lambda_basic
end



all(a:TERM,n:NATURAL)
        -- Zero upshift
    ensure
        a.up_from(n,0) = a
    inspect
        a
    case var(i)
        if i < n
        else if i = n
        else
    end



all(a:TERM, k,n,m:NATURAL)
        -- Lemma: Cumulate 'up_from'.
    ensure
        a.up_from(k,n).up_from(k,m) = a.up_from(k,n+m)
    inspect
        a
    case var(i)
        if i < k
            via [ var(i) ]
        else
            assert
                not (i + n < k)
            via [ var(i+n+m) ]
    end


all(k,l,m,n:NATURAL, a:TERM)
        -- Lemma: Double 'up_from'.
    require
        k <= m
    ensure
        a.up_from(m,n).up_from(k,l) = a.up_from(k,l).up_from(m+l,n)
    inspect
        a
    case var(i)
        if i < k
            assert
                i < m
                i < m + l
            via [ var(i) ]
        else if i < m
            assert
                i + l < m + l
            via [ var(i+l) ]
        else
            -- not (i < m), i.e. k <= m <= i
            assert
               not (i + n < k)
               not (i + l < m + l)
               n + l = l + n
            via [ var(i + n + l)
                , var(i + (n + l))
                , var(i + (l + n))
                , var(i + l + n)
                ]
    case lam(a)
        assert
            a.up_from(m+1,n).up_from(k+1,l)
            = a.up_from(k+1,l).up_from(m+1+l,n)  -- ind hypo specialized

            ensure
                m + 1 + l = m + l + 1
            assert
                1 + l = l + 1
            via [ m + (1 + l)
                , m + (l + 1)
                ]
            end

        via [ lam( a.up_from(m+1,n).up_from(k+1,l) )      -- def 'up_from'
            , lam( a.up_from(k+1,l).up_from(m+1+l,n) )    -- ind hypo
            , lam( a.up_from(k+1,l).up_from(m+l+1,n) )    -- commutativity '+'
            ]
    end





all(k,m,n:NATURAL, a,b:TERM)
        {: Lemma: Swap substitution and upshifting below substitution

           Instead of substituting a variable by some expression and then
           upshifting from below that variable is equivalent to first do the
           upshifting and then substitute the upshifted variable by the
           upshifted expression.
        :}
    require
        m <= k
    ensure
        a.sub(k,b).up_from(m,n)
        = a.up_from(m,n).sub(k+n,b.up_from(m,n))
    inspect
        a
    case var(i)
        if i < m
            assert
                i < k
                i < k + n
            via [ var(i) ]
        else if i < k
            assert
               i + n < k + n
            via [ var(i+n) ]
        else if i = k
            assert
                i + n = k + n
                not (i + n < k + n)
            via [ b.up_from(m,n) ]
        else
            assert
                m < i
                not (i - 1 < m)
                not (i < m)
                not (i+n < k+n)
                not (i+n = k+n)
                i - 1 + n = i + n - 1
            via [ var(i-1+n)
                , var(i+n-1)]
    case lam(x)
        {: goal: lam(x).sub(k,b).up_from(m,n)
                  = lam(x).up_from(m,n).sub(k+n,b.up_from(m,n))

        :}
        assert
            x.sub(k+1,b.up).up_from(m+1,n)  -- ind hypo
            = x.up_from(m+1,n).sub(k+1+n,b.up.up_from(m+1,n))

            lam(x).up_from(m,n).sub(k+n,b.up_from(m,n))
            =  -- def up_from, sub
            lam( x.up_from(m+1,n).sub(k+n+1,b.up_from(m,n).up) )

            ensure
                k + 1 + n = k + n + 1
            via [ k + (1 + n)
                , k + (n + 1)
                ]
            end

            ensure
                b.up.up_from(m+1,n) = b.up_from(m,n).up
            via [ b.up_from(0,1).up_from(m+1,n)
                , b.up_from(m,n).up_from(0,1)
                ]
            end

        via [ lam( x.sub(k+1,b.up).up_from(m+1,n) )
              -- ind hypo
            , lam( x.up_from(m+1,n).sub(k+1+n,b.up.up_from(m+1,n)) )
            , lam( x.up_from(m+1,n).sub(k+n+1,b.up_from(m,n).up) )
            ]
    end




all(k,m,n:NATURAL, a,b:TERM)
        -- Lemma: Swap substitution and upshifting above substitution
    require
        k <= m
    ensure
        a.sub(k,b).up_from(m,n)
        = a.up_from(m+1,n).sub(k,b.up_from(m,n))
                --  ^ shifts above k
                --  k is not affected
    inspect
        a
    case var(i)
        if i < k
            assert
                i < m
                i < m + 1
            via [ var(i) ]
        else if i = k
            assert
                i < m + 1
            via [ b.up_from(m,n) ]
        else if i - 1 < m
            assert
                i - 1 <= m
                i <= m + 1
                i < m + 1
            via [ var(i-1) ]
        else
            assert
                true
                not (i < m + 1)
                k <= i
                not (i + n < k)
                not (i + n = k)
                i - 1 + n = i + n - 1
            via [ var(i-1+n)
                , var(i+n-1)
                ]
    case lam(x)
        assert
            x.sub(k+1,b.up).up_from(m+1,n)
            = x.up_from(m+1+1,n).sub(k+1,b.up.up_from(m+1,n))  -- ind hypo

        ensure
            b.up_from(m,n).up = b.up.up_from(m+1,n)
        via [ b.up_from(m,n).up_from(0,1)
            , b.up_from(0,1).up_from(m+1,n)
            ]
        end

        via [ lam( x.sub(k+1,b.up).up_from(m+1,n) )   -- def 'sub' 'up_from'
            , lam( x.up_from(m+1+1,n).sub(k+1,b.up.up_from(m+1,n)) )  -- ind hypo
            , lam( x.up_from(m+1+1,n).sub(k+1,b.up_from(m,n).up)  )
            ]
    end


all(n,k:NATURAL, a,b:TERM)
        -- Lemma: Substitute non present variables.
    ensure
        a.up_from(n,k+1).sub(n+k,b) = a.up_from(n,k)
    inspect
        a
    case var(i)
        if i < n
            assert
                i < n + k
            via [ var(i) ]
        else
            assert
                n <= i
                n + k <= i + k
                n + k < i + k + 1
                not (i + (k + 1) < n + k)
                not (i + (k + 1) = n + k)
            via [ var(i+k+1-1)
                , var(i+k)
                ]
    case lam(x)
        assert
            x.up_from(n+1,k+1).sub(n+1+k,b.up) = x.up_from(n+1,k)  -- ind hypo

            ensure
                n + k + 1 = n + 1 + k
            assert
               k + 1 = 1 + k
            via [ n + (k + 1)
                , n + (1 + k)
                ]
            end
        via [ lam ( x.up_from(n+1,k+1).sub(n+k+1,b.up) )
            , lam ( x.up_from(n+1,k+1).sub(n+1+k,b.up) )
            , lam ( x.up_from(n+1,k) )
            ]
    end




all(k,n:NATURAL, a,b,c:TERM)
    {: Lemma: Swap substitutions
    :}
    require
        k <= n
    ensure
        a.sub(k,b).sub(n,c.up(k)) = a.sub(n+1,c.up(k).up).sub(k,b.sub(n,c.up(k)))
    inspect
        a
    case var(i)
        if i < k
            assert
                i < n
                i < n + 1
            via [ var(i) ]
        else if i = k
            assert
                i < n + 1
            via [ b.sub(n,c.up(k)) ]
        else if i - 1 < n
            assert
                i < n + 1
            via [ var(i-1) ]
        else if i - 1 = n
            assert
                i = n + 1
                not (i < n+1)
                ensure
                    c.up_from(0,k+1) = c.up(k).up
                via [ c.up_from(0,k).up_from(0,1) ]
                end
                0 + k = k
            via [ c.up(k)
                , c.up_from(0,k)
                , c.up_from(0,k+1).sub(0+k,b.sub(n,c.up(k)))
                , c.up(k).up.sub(k,b.sub(n,c.up(k)))
                ]
        else
            assert
                not (i < n + 1)
                not (i = n + 1)
                not (i - 1 < k)
                not (i - 1 = k)
            via [ var(i-1-1) ]
    case lam(x)
        {: goal: lam(x).sub(k,b).sub(n,c.up(k))
                  = lam(x).sub(n + 1,c.up(k).up).sub(k,b.sub(n,c.up(k)))
        :}
        assert
            k <= n

            x.sub(k+1,b.up).sub(n+1,c.up(k+1))  -- ind hypo
            = x.sub(n+1+1,c.up(k+1).up).sub(k+1,b.up.sub(n+1,c.up(k+1)))

            ensure
                c.up(k).up = c.up(k+1)
            via [ c.up_from(0,k).up_from(0,1)
                , c.up_from(0,k+1)
                ]
            end

            lam(x).sub(n + 1,c.up(k).up).sub(k,b.sub(n,c.up(k)))
            -- rhs of goal
            = lam( x.sub(n+1+1,c.up(k).up.up).sub(k+1,b.sub(n,c.up(k)).up ) )

        ensure
            b.up.sub(n+1,c.up(k+1)) = b.sub(n,c.up(k)).up
        via [ b.up_from(0,1).sub(n+1,c.up(k).up)
            , b.up_from(0,1).sub(n+1,c.up(k).up_from(0,1))
            , b.sub(n,c.up(k)).up_from(0,1)
            ]
        end

        via [ lam( x.sub(k+1,b.up).sub(n+1,c.up(k).up) )
            , lam( x.sub(k+1,b.up).sub(n+1,c.up(k+1)) )
            , lam( x.sub(n+1+1,c.up(k+1).up).sub(k+1,b.up.sub(n+1,c.up(k+1))) )
            , lam( x.sub(n+1+1,c.up(k).up.up).sub(k+1,b.sub(n,c.up(k)).up) )
            ]
    end

all(a,b,c:TERM, n:NATURAL)
        -- Swap substitutions base case
    ensure
        a.sub(b).sub(n,c) = a.sub(n+1,c.up).sub(b.sub(n,c))
    assert
        c.up_from(0,0) = c
        c.up(0) = c
    via [ a.sub(0,b).sub(n,c.up(0))
        , a.sub(n+1,c.up(0).up).sub(0,b.sub(n,c.up(0)))
        ]
    end
