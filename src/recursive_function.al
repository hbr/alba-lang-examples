use
    alba.base.predicate -- should already be in natural and list
    alba.base.natural
    alba.base.list
end



class
    RECURSIVE
create
    zero
    successor
    compose (g:RECURSIVE, hs:[RECURSIVE])
    recurse (f,g:RECURSIVE)
    minimize (p:RECURSIVE)
end


primitives: ghost {RECURSIVE,NATURAL}
    = {(pr):
          pr(zero,0)
          ,
          pr(successor,1)
          ,
          all(g,n,hs,m) pr(g,n) ==>
                   hs.length = n ==>
                   (all(h) h in hs ==> pr(h,m)) ==>
                   pr(compose(g,hs),m)
      }




all(n:NATURAL)
    ensure
        some(a:[NATURAL]) a.length = n
    inspect
        n
    case 0
        assert
            ([]:[NATURAL]).length = 0
    case k.successor
        via some(a:[NATURAL]) a.length = k
        assert
            (0 ^ a).length = k.successor
    end






{: Recursive Functions
   ===================

The recursive functions are the computable functions of type [NATURAL] -> NATURAL.

Each recursive function maps a list of natural arguments to a natural
number. The list of arguments can be empty to represent constants.

:}

has_arity(f:[NATURAL]->NATURAL, n:NATURAL): ghost BOOLEAN
        -- Does the function 'f' have arity 'n'?
    -> f.domain = {l: l.length = n}


all(n,m:NATURAL, f:[NATURAL]->NATURAL)
    require
        f.has_arity(n)
        f.has_arity(m)
    ensure
        n = m
    via some(a:[NATURAL]) a.length = n
    assert
        a in f.domain
        a in {a: a.length = m}
    end


is_function(f:[NATURAL]->NATURAL): ghost BOOLEAN
    -> some(n) f.has_arity(n)


arity(f:[NATURAL]->NATURAL): ghost NATURAL
    require
        f.is_function
    ensure
        f.has_arity(Result)
    end



zero: ([NATURAL] -> NATURAL)
    = agent (a)
         require
             a as []
         ensure
             -> 0
         end

successor: ([NATURAL] -> NATURAL)
    = agent (a)
         require
             a as [_]
         ensure
             -> a.head + 1
         end


projector (i,n:NATURAL): ([NATURAL] -> NATURAL)
        -- Project a list of n naturals to its ith element.
    require
        i < n
    ensure
        -> agent (a)
               require
                   a.length = n
               ensure
                   -> a[i]
               end
    end


{: Function Composition
   ====================  :}

has_arity (fs:[[NATURAL]->NATURAL], n:NATURAL): ghost BOOLEAN
    -> all(f) f in fs ==> f.has_arity(n)



is_function_list(fs:[[NATURAL]->NATURAL]): ghost BOOLEAN
    -> some(n) fs.has_arity(n)


all(a:[NATURAL], h:[NATURAL]->NATURAL,hs,fs:[[NATURAL]->NATURAL])
    require
        fs.has_arity(a.length)
        fs = h ^ hs
    ensure
        a in h.domain
    assert
        h.has_arity(a.length)
    end



all(a:[NATURAL], h:[NATURAL]->NATURAL,hs,fs:[[NATURAL]->NATURAL])
    require
        fs.has_arity(a.length)
        fs = h ^ hs
    ensure
        hs.has_arity(a.length)
    end


all(a:[NATURAL], f:[NATURAL]->NATURAL,fs:[[NATURAL]->NATURAL])
    require
        (f ^ fs).has_arity(a.length)
    ensure
        fs.has_arity(a.length)
    end


all(a:[NATURAL], f:[NATURAL]->NATURAL,fs:[[NATURAL]->NATURAL])
    require
        (f ^ fs).has_arity(a.length)
    ensure
        fs.is_function_list
    end



all(a:[NATURAL], h:[NATURAL]->NATURAL,hs,fs:[[NATURAL]->NATURAL])
    require
        fs.has_arity(a.length)
        fs = h ^ hs
    ensure
        hs.is_function_list
    assert
        hs.has_arity(a.length)
    end



all(fs:[[NATURAL]->NATURAL], h:[NATURAL]->NATURAL)
    require
        fs.is_function_list
        h in fs
    ensure
        h.is_function
    via some(n) fs.has_arity(n)
    assert
        h.has_arity(n)
    end





[](fs:[[NATURAL]->NATURAL], a:[NATURAL]): [NATURAL]
        -- Apply each function in the function list 'fs' to the list of
        -- arguments [a] and return the list of results.
    require
        fs.is_function_list
        fs.has_arity(a.length)
    ensure
        -> inspect
               fs
           case [] then
               []
           case h ^ hs then
               h(a) ^ hs[a]
    end


all(fs:[[NATURAL]->NATURAL], a:[NATURAL])
    require
        fs.is_function_list
        fs.has_arity(a.length)
    ensure
        fs[a].length = fs.length
    inspect
        fs
    case f ^ fs
    via [ (f ^ fs)[a].length
        , (f(a) ^ fs[a]).length
        , fs[a].length + 1
        , fs.length + 1
        , (f ^ fs).length
        ]
    end


compose (g:[NATURAL]->NATURAL, hs:[[NATURAL]->NATURAL]):([NATURAL]->NATURAL)
    {: Compose the function 'g' with the list of functions [h1,h2,...] i.e.
       return the function which first applies its arguments to each of the
       functions h1,h2,... and then feed the list of results into 'g'.:}
    require
         g.is_function
         g.has_arity(hs.length)
         hs.is_function_list
    ensure
         -> agent (a)
                require
                    hs.has_arity(a.length)
                ensure
                    -> g(hs[a])
                end
    end




{: Primitive Recursion
   ===================  :}


compute_recursive (g,h:[NATURAL]->NATURAL, n:NATURAL, a:[NATURAL]): NATURAL
    require
        g.has_arity(a.length)
        h.has_arity(a.length + 2)
    ensure
        -> inspect
               n
           case 0 then
               g(a)
           case k.successor then
               h(compute_recursive(g,h,k,a) ^ k ^ a)
    end

all(g:[NATURAL]->NATURAL, x:NATURAL, xs:[NATURAL])
    require
        g.is_function
        (x ^ xs).length = g.arity + 1
    ensure
        g.has_arity(xs.length)
    assert
        xs.length = g.arity
    end

all(g,h:[NATURAL]->NATURAL, x:NATURAL, xs:[NATURAL])
    require
        g.is_function
        h.has_arity(g.arity + 2)
        (x ^ xs).length = g.arity + 1
    ensure
        h.has_arity(xs.length + 2)
    assert
        xs.length = g.arity
    end


recursive (g,h:[NATURAL]->NATURAL): ([NATURAL]->NATURAL)
    require
        g.is_function
        h.has_arity(g.arity + 2)
    ensure
        -> agent (a)
               require
                   a.length = g.arity + 1
               ensure
                   -- -> compute_recursive(g,h,a.head,a.tail) won't work
                   --    precondition a as _ ^ _ fails
                   -> inspect
                          a
                      case x ^ xs then
                          compute_recursive(g,h,x,xs)
               end
    end


primitive_recursives: ghost {[NATURAL]->NATURAL}
    = {(p): zero in p
            ,
            successor in p
            ,
            all(i,n) i < n ==> projector(i,n) in p
            ,
            all(g,hs) g.is_function ==>
                      g.has_arity(hs.length) ==>
                      hs.is_function_list ==>
                      compose(g,hs) in p
            ,
            all(g,h) g.is_function ==>
                     h.has_arity(g.arity + 2) ==>
                     recursive(g,h) in p
      }





{: Minimization
   ============  :}


minimize (f:[NATURAL]->NATURAL): ghost ([NATURAL]->NATURAL)
    require
        f.is_function
        all(a) f.has_arity(a.length+1) ==> {n: f(n ^ a) = 0}.has_some
    ensure
        -> agent (a)
               require
                   f.has_arity(a.length+1)
               ensure
                   -> {n: f(n ^ a) = 0}.least
               end
    end



recursives: ghost {[NATURAL]->NATURAL}
    = {(p): zero in p
            ,
            successor in p
            ,
            all(i,n) i < n ==> projector(i,n) in p
            ,
            all(g,hs) g.is_function ==>
                      g.has_arity(hs.length) ==>
                      hs.is_function_list ==>
                      compose(g,hs) in p
            ,
            all(g,h) g.is_function ==>
                     h.has_arity(g.arity + 2) ==>
                     recursive(g,h) in p
            ,
            all(f) f.is_function ==>
                   0 < f.arity ==>
                   (all(a) f.has_arity(a.length+1) ==>
                           {n: f(n ^ a) = 0}.has_some)
                   ==>
                   minimize(f) in p
      }
