use
    alba.base.list
    alba.base.linear_order
    alba.base.option
end

L: LINEAR_ORDER


sorted_lists: ghost {[L]}
    = {(sorted):
           [] in sorted,
           all(x) [x] in sorted,
           all(x,y,a) x <= y ==> y ^ a in sorted ==> x ^ y ^ a in sorted
      }


{: Merging of Sorted Lists
   =======================
:}
merge (a,b:[L]): [L]
        -- Merge two sorted lists.
    -> inspect
           a, b
       case [], _ then
           b
       case _, [] then
           a
       case x^xs, y^ys then
           if x <= y then
               x ^ merge(xs,b)
           else
               y ^ merge(a,ys)


all(a,b:[L])
    require
        a in sorted_lists
        b in sorted_lists

    ensure
        merge(a,b) in sorted_lists

    inspect
        a in sorted_lists
    case all(x:L) [x] in sorted_lists
        (inspect
            b in sorted_lists
         case all(u:L) [u] in sorted_lists
             if x <= u
             else
         case all(u:L,v,d) u <= v ==>
                            v ^ d in sorted_lists ==>
                            u^v^d in sorted_lists
             if x <= u
             else if x <= v
             else
        )
    case all(x,y:L,c) x <= y ==>
                       y ^ c in sorted_lists ==>
                       x ^ y ^ c in sorted_lists
        {: ind hypo:     all(b:[L]) y ^ c in sorted_lists ==>
                                    b in sorted_lists ==>
                                    merge(y ^ c,b) in sorted_lists

        :}
        (inspect
            b in sorted_lists
         case all(u:L) [u] in sorted_lists
             -- goal: merge(x ^ y ^ c,[u]) in sorted_lists
             if x <= u
                 assert
                     merge(x^y^c,[u]) = x ^ merge(y^c,[u])
                     merge(y^c,[u]) in sorted_lists -- ind hypo
                 if y <= u
                     assert
                         merge(y^c,[u]) = y ^ merge(c,[u])
                 else
                     assert
                         merge(y^c,[u]) = u ^ y ^ c
             else
         case all(u:L,v,d) u <= v ==>
                            v ^ d in sorted_lists ==>
                            u^v^d in sorted_lists
             -- goal: merge(x^y^c,u^v^d) in sorted_lists
             if x <= u
                 assert
                      merge(x^y^c,u^v^d) = x^merge(y^c,u^v^d)
                      merge(y^c,u^v^d) in sorted_lists
                 if y <= u
                     assert
                          merge(y^c,u^v^d) = y^merge(c,u^v^d)
                 else
             else
                 if x <= v
                 else
        )
    end



{: Stacks of Sorted Lists
   ======================
:}

sorted_stacks: ghost {[OPTION[[L]]]}
    = {(p):
           [] in p
           ,
           all(stack) stack in p ==> none^stack in p
           ,
           all(a,stack) a in sorted_lists ==>
                        stack in p ==>
                        value(a)^stack in p
      }



into_stack (a:[L], stack: [OPTION[[L]]]): [OPTION[[L]]]
        -- Merge the sorted list 'a' into the stack.
    -> inspect
           stack
       case [] then
           [value(a)]
       case none ^ rest then
           value(a) ^ rest
       case value(b) ^ rest then
           none ^ into_stack(merge(a,b),rest)


all(a:[L], stack:[OPTION[[L]]])
     require
          stack in sorted_stacks
          a in sorted_lists
     ensure
          a.into_stack(stack) in sorted_stacks
     inspect
          stack in sorted_stacks
     end


make_stack(a:[L], stack: [OPTION[[L]]]): [OPTION[[L]]]
    -> inspect
           a
       case [] then
           []
       case x ^ xs then
           make_stack(xs, [x].into_stack(stack))

all(a:[L], stack:[OPTION[[L]]])
     require
          stack in sorted_stacks
     ensure
          make_stack(a,stack) in sorted_stacks
     inspect
          a
     end




{: Merge Sort
   ===========
:}

merge_stack (stack: [OPTION[[L]]]): [L]
    -> inspect
           stack
       case [] then
           []
       case none ^ rest then
           merge_stack(rest)
       case value(a) ^ rest then
           merge(a, merge_stack(rest))

all(stack:[OPTION[[L]]])
     require
          stack in sorted_stacks
     ensure
          merge_stack(stack) in sorted_lists
     inspect
          stack in sorted_stacks
     end


merge_sort (a:[L]): [L]
    -> make_stack(a,[]).merge_stack

all(a:[L])
    ensure
        a.merge_sort in sorted_lists
    end

{:
        make_stack([6,2,3,1,5,0,7,8])

        stack (reversed)                              unprocessed list

        []                                            [6,2,3,1,5,0,7,8]
        [value([6])]                                  [2,3,1,5,0,7,8]
        [value([2,6]),none]                           [3,1,5,0,7,8]
        [value([2,6]),value([3])]                     [1,5,0,7,8]
        [value([1,2,3,6]),none,none]                  [5,0,7,8]
        [value([1,2,3,6]),none,value([5])]            [0,7,8]
        [value([1,2,3,6]),value([0,5]),none]          [7,8]
        [value([1,2,3,6]),value([0,5]),value([7])]    [8]
        [value([0,1,2,3,5,6,7,8]),none,none,none]     []

:}