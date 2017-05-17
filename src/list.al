use
    alba.base.core
end


A: ANY


-- concatenation -------------------------------
(+) (a,b:[A]): [A]
    -> inspect
           a
       case [] then
           b
       case x ^ xs then
           x ^ (xs + b)


all(a:[A])
    ensure
        a + [] = a
    inspect
        a
    end

all(a,b,c:[A])
    ensure
        a + b + c = a + (b + c)
    inspect
        a
    end



-- reversal -------------------------------
(-) (a:[A]): [A]
    -> inspect
           a
       case [] then
           a
       case x ^ xs then
           -xs + [x]



all(a,b:[A])
        -- Reversal of concatenated lists.
    ensure
        - (a + b) = -b + -a
    inspect
        a
    case x ^ xs
        -- hypo:  - (xs + b) = -xs + -b
        -- goal:  -(x ^ xs + b) = -b + - x ^ xs
        via [ -(x ^ xs + b)
            , - x ^ (xs + b)           -- def '+'
            , - (xs + b) + [x]         -- def '-'
            , -b + - xs + [x]          -- ind hypo
            , -b + (- xs + [x])        -- assoc
            , -b + - x ^ xs            -- def '-'
            ]
    end


all(a:[A])
        -- List reversal is an involution.
    ensure
        - - a = a
    inspect
        a
    case x ^ xs
        -- hypo: - - xs = xs
        -- goal: - - x ^ xs = x ^ xs
        via [ - - x ^ xs
            , - (-xs + [x])       -- def '-'
            , -[x] + - - xs       -- - (a + b) = - b + - a
            , -[x] + xs           -- ind hyp
            , x ^ xs              -- def '+'
            ]
    end



-- permutation -------------------------------
permutation: ghost {[A], [A]}
    = {(r):
             r([],[])                                 -- empty
             ,
             all(x,a,b) r(a,b) ==> r(x^a, x^b)        -- prefix element
             ,
             all(x,y,a) r(x^y^a, y^x^a)               -- swap adjacent
             ,
             all(a,b,c) r(a,b) ==> r(b,c) ==> r(a,c)  -- transitive
      }


all(a:[A])
        -- 'permutation' is reflexive
    ensure
        permutation(a,a)
    inspect
        a
    end


all(a,b:[A])
        -- 'permutation' is symmetric
    require
        permutation(a,b)
    ensure
        permutation(b,a)
    inspect
        permutation(a,b)
    end


all(x:A, a,b:[A])
    require
        permutation(a,b)
    ensure
        permutation(x^a, x^b)
    end


all(x:A, a:[A])
        -- swap first and last element
    ensure
        permutation (x ^ a, a + [x])
    inspect
        a
    case y ^ a
        -- goal: permutation(x ^ y ^ a, y ^ a + [x])
        -- hypo: all(x) permutation(x ^ a, a + [x])
        via [ x ^ y ^ a
            , y ^ x ^ a        -- swap adjacent
            , y ^ (a + [x])    -- prefix element, ind hypo
            , y ^ a + [x]      -- def '+'
            ]
    end
