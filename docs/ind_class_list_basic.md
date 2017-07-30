# List Basics

The class `LIST` is defined in the module `core` of the library
`alba.base`. We use this definition here.

    use
        alba.base.core
    end

    {: The use clause makes the following declaration available:

       class
           LIST[A]
       create
           []
           (^) (x:A, xs:[A])   -- [A] is a shorthand for LIST[A]
       end
    :}

    A: ANY  -- Since class variables have file scope we need our own
            -- declaration of a class variable here.



#### Concatenation

We declare concatenation of lists as a recursive function.

    (+) (a,b:[A]): [A]
        -> inspect
               a
           case [] then
               b
           case x ^ xs then
               x ^ (xs + b)

Remember that the Alba compiler can evaluate recursive functions as long as it
can decide the case. Therefore `[] + b` is evaluates to `b` and `x ^ a + b`
evaluates to x ^ (a + b) immediately. Therefore the following two theorems are
trivially valid.

    all(a:[A])
        ensure
            [] + a = a      -- proved by evaluation of the left hand side
        end

    all(x:A, a,b:[A])
        ensure
            x ^ a + b = x ^ (a + b) -- proved by evaluation of the left hand side
        end

It is useless to write them down because the compiler does the job in any
complicated context by evaluation and does not need these theorems.

However the compiler is unable to evaluate the expression `a + []` to `a`
because none of the pattern in the definition of `+` matches. I.e. the
compiler cannot prove `a + [] = a` automatically.

The class `LIST` has only two constructors `[]` and `^`. If `a` is a list then
it must have been constructed by one of the constructors.

If we substitute `a` by `[]` then `[] + []` evaluates to `[]`. I.e. the case
with the empty list is trivial.

If we substitute `a` by `x^b` then `x^b + []` evaluates to `x ^ (b + [])`.  In
an induction proof we get the induction hypothesis `b + [] = b` for free and
can further evaluate `x ^ (b + [])` to `x ^ b`. I.e. the compiler can prove `x
^ b + [] = x ^ b`.

I.e. in order to prove `a + [] = a` we have to instruct the compiler to do an
induction of `a` i.e. to do a case analysis on the possible constructions of
`a` and use possible induction hypotheses.

    all(a:[A])
        ensure
            a + [] = a
        inspect
            a
        end


In a similar manner we can prove that concatenation of lists is associative.


    all(a,b,c:[A])
        ensure
            a + b + c = a + (b + c)
        inspect
            a
        end




#### List Reversal

The definition of list reversal is straightforward.

    (-) (a:[A]): [A]
        -> inspect
               a
           case [] then
               a
           case x ^ xs then
               -xs + [x]

In order to reverse a nonempty list we reverse its tail and append the head
element at the end. We use the operator `-` for list reversal because list
reversal is some kind of negation, i.e. `- a` is the list `a` reversed.

The definition describes how to reverse a list of the form `x ^ a`. But what
is the reverse of `a + b`? Clearly it should be the lists `a` and `b` reversed
separately and then concatenated in the reversed order. I.e. we shall be able
to prove

    - (a + b) = -b + -a

We try induction on `a` and see that for the empty list `a` the prove is
trivial since `-([] + b)` is `-b` and `-b + -[]` is `-b` as well.

Therefore we can concentrat on the case that `a` has been constructed as `x ^
xs`. This is the induction case and we get the induction hypothesis that `xs`
already satisfies the goal.

    - (xs + b) = -b + -xs        -- induction hypothesis

The goal in the induction case is

    - (x^xs + b) = -b + -x^xs    -- induction goal

We can transform the left hand side step by step into the right hand side.

    -(x^xs + b)            -- left hand side
    -x^(xs + b)            -- definition of '+'
    -(xs + b) + [x]        -- definition of '-'
    -b + -xs + [x]         -- induction hypothesis
    -b + (-xs + [x])       -- associativity of lists
    -b + -x^xs             -- definition of '-' in reverse direction

Note that '+' and '-' are addition operators which have a lower precedence
than the prefix operator `^`.


A formal proof in Alba instructs the compiler to do induction on `a` and
guides the transformation of the left hand side into the right hand side in
the induction case.

    all(a,b:[A])
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


In a similar manner it is easy to prove that inversion of a list applied two
times results in the original list.



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


#### Performance Improvement by Tail Recursion

The recursive definition of list reversal as shown above is computationally
not very efficient. It iterates over the whole list to reverse and has to
append at every level of this iteration the head element to the end. This
algorithm is quadratic on the length of the list. There should be an algorithm
which takes only linear time.

Intuitively we take the first element of the list and prepend it to an empty
list. Then we take the next element and prepend it to the previous list and so
on.

In order to do that we need some variable to store the intermediate
results. Let's call this accumulator variable `acc`. Our improved algorithm
shall prepend the reversed remainder of the list in front of the accumulator
variable i.e. it has to satisfy the invariant

    a.reverse_prepend(acc) = -a + acc

If we can design such a function we can reverse any list `a` by calling
`a.reverse_prepend([])`.

It is not difficult to define such a function.

    reverse_prepend(a,acc:[A]): [A]
        -> inspect
               a
           case [] then
               acc
           case x ^ xs then
               xs.reverse_prepend(x ^ acc)


Although clear by intutition we shall be able to prove that `reverse_prepend`
satisfies the stated invariant. We can prove the invariant by induction on the
list to be reversed.


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

The case of an empty list is a triviality and requires the proof engine only
to evaluate the goal. The inductive case needs some annotations. As before we
transform the left hand side step by step into the right hand side.

Note that Alba's prove engine does not prove the goal

    a.reverse_prepend(acc) = -a + acc

for all `a`. It proves the stronger goal

    all(acc) a.reverse_prepend(acc) = -a + acc

Therefore we get a stronger induction hypothesis in the inductive case. In our
prove the stronger induction hypothesis is essential. In the via proof we
could not do the transition from step 2 to step 3 without the
generalization. We have to apply the induction hypothesis to `x ^ acc` and not
to `acc`.

Now comes the easy part to show that we can use `reverse_prepend` to compute
the reverse of a list.

    all(a:[A])
        ensure
            a.reverse_prepend([]) = -a
        via
            [ -a + [] ]
        end


Note that `reverse_prepend` is does not only perform in linear time. It is
also tail recursive. A recursive function is called tail recursive if the
result of a recursive call directly represents the desired result. No more
operations on the return value of a recursive call are needed.

A tail recursive function has the advantage that no stack is needed at runtime
to compute the function. I.e. our tail recursive variant for list reversal is
not only more time efficient, it is more space efficient than the recursive
version as well.



<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
