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
    case x ^ a
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



-- tail recursive reversal -------------------------------
reverse_prepend (a:[A], acc:[A]): [A]
        -- The reversed list 'a' prepended in front of 'acc'.
    -> inspect
           a
       case [] then
           acc
       case x ^ xs then
           xs.reverse_prepend(x ^ acc)



all(a,acc:[A])
    ensure
        a.reverse_prepend(acc) = -a + acc
    inspect
        a
    case x ^ xs
        -- hypo  all(acc) xs.reverse_prepend(acc) = -xs + acc
        -- goal: (x^xs).reverse_prepend(acc) = -x^xs + acc
        via [
              (x ^ xs).reverse_prepend(acc)
            , xs.reverse_prepend(x ^ acc)    -- def 'reverse_prepend'
            , -xs + x^acc                    -- ind hypo
            , -xs + ([x] + acc)              -- def '+'
            , -xs + [x] + acc                -- assoc
            , - x^xs + acc                   -- def '-'
            ]
    end

all(a:[A])
    ensure
        a.reverse_prepend([]) = -a
    via
        [ -a + [] ]
    end



-- tail recursive concatenation -------------------------------
concat(a,b:[A]): [A]
    -> a.reverse_prepend([]).reverse_prepend(b)

all(a,b:[A])
    ensure
        concat(a,b) = a + b
    via [
        (-a).reverse_prepend(b),
        (- - a) + b
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
