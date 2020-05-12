:- module(optimum,[generate_schedule/1]).

%:- use_module(library(clpfd)).

pallets_per_truck(4).

% Item, Quantity
items_per_pallet(1,3).
items_per_pallet(2,2).
items_per_pallet(3,2).

% Item, Supplier, Remainder
item_supplier_remainder(3,2,35).
item_supplier_remainder(1,3,-20).
item_supplier_remainder(2,3,-2).
item_supplier_remainder(1,4,-10).

% items
items(Items) :-
    findall(I, item_supplier_remainder(I,_,_), Items_Unsorted),
    sort(Items_Unsorted,Items).

order_pallet_count([],0).
order_pallet_count([_-Pallets|Rest],Count) :-
    order_pallet_count(Rest,Rest_Count),
    Count is Pallets + Rest_Count.

increment_item_in_order(Item,Count,[],[Item-Count]).
increment_item_in_order(Item,Count,[Item-Pallets|Rest],[Item-New_Pallets|Rest]) :-
    New_Pallets is Pallets + Count.
increment_item_in_order(Item,Count,[I-Count|Rest],[I-Count|Order]) :-
    \+ Item = I,
    increment_item_in_order(Item,Count,Rest,Order).

% Yes, this just deletes from the order schedule, but fails if it can not,
% so acts as a search as well.
get_truck(truck(Truck,Order),Order,Order_Rest) :- 
    delete(Order,truck(Truck,Order),Order_Rest).
    
/* 
 * :- type pallets == integer.
 * :- type item == integer.
 * :- type truck ---> truck(supplier,list(pair(item,pallets))).
 */ 
add_pallets(Item,Supplier,Pallets,Schedule,Schedule_Out) :-
    pallets_per_truck(Pallets_Per_Truck),

    (   get_truck(truck(Supplier,Order),Schedule,Rest_of_Schedule),
        order_pallet_count(Order,Count),
        % Still room in this truck
        Count < Pallets_Per_Truck
    % some of the truck is filled
    ->  Remaining_Room is Pallets_Per_Truck - Count
    % none of this truck is filled
    ;   Remaining_Room is Pallets_Per_Truck,
        Rest_of_Schedule = Schedule,
        Order = []
    ),
    
    % check to see if we need more trucks.
    (   Remaining_Room < Pallets
    % we need more trucks..
    ->  increment_item_in_order(Item,Remaining_Room,Order,New_Order),
        Schedule_2 = [truck(Supplier,New_Order)|Rest_of_Schedule],
        Remaining_Pallets is Pallets - Remaining_Room,
        add_pallets(Item,Supplier,Remaining_Pallets,Schedule_2,Schedule_Out)
    % we don't need trucks
    ;   increment_item_in_order(Item,Remaining_Room,Order,New_Order),
        Schedule_Out = [truck(Supplier,New_Order)|Rest_of_Schedule]
    ). 

add_items(Item,Supplier,Remainder,Schedule,Schedule2) :-
    items_per_pallet(Item,Number),
    Pallets is ceiling(-Remainder / Number),
    add_pallets(Item,Supplier,Pallets,Schedule,Schedule2).

generate_schedule(Schedule) :-
    items(Items),
    generate_schedule(Items,[],Schedule).

generate_schedule([],Schedule,Schedule).
generate_schedule([Item|Items],Schedule,New_Schedule) :-
    item_supplier_remainder(Item,Supplier,Remainder),
    (   Remainder < 0
    ->  add_items(Item,Supplier,Remainder,Schedule,Schedule2),
        generate_schedule(Items,Schedule2,New_Schedule)
    ;   generate_schedule(Items,Schedule,New_Schedule)
    ).

       
/* 
 * Supplier, Item, Pallets
 * [S,I,P]
 */

/*
solution(Suppliers_Item,_Pallets) :-
    findall([I,S,R],item_supplier_remainder(I,S,R),ISR),
    
    item_supplier_remainder(Item,Suppplier,Remainder),
    
    R <# 0,

    Number_Trucks in 0..sup,
    
    S <# N + R 
    
    item_supplier_remainder(J,Supplier,Q),


choose_valid_order(Valid) :-    
   isr(Item,Supplier,Remainder), 
   Remainder <= 0, 
   


choose_valid_order(Valid),
pallets_per_truck(Pallets_per_truck),
Number_of_Trucks_Supplier_I #= celing(Number_Of_Pallets_Supplier_I / Pallets_per_truck),


    
*/
