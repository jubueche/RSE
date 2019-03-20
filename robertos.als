/*
 * Signatures
 *
 * Your model should contain the following (and potentially other) signatures.
 * If necessary, you have to make some of the signatures abstract and
 * make them extend other signatures.
 * 
 */

 /*
 *  Hints: You may need to define a Bool signature when crafting the following sig. 
 *  Consider searching online to find tutorials on this topic.
 *  
 */

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Employee { 
	employeeManagementSystem: ManagementSystem
}

sig Intern extends Employee {
	internDelivery: some Delivery,
	isChef: one Bool
} {
//courierDelivery.deliveredEmployee = Intern
}


sig Chef extends Employee {
	chefOrder: set Order,
	chefPizza: some Pizza //Check that relation
}

sig Courier extends Employee {
	courierDelivery: some Delivery
}

one sig Manager {
	managerAnalytics: one Analytics
}

sig Analytics {
	analyticsManager: one Manager,
	analyticsManagementSystem: one ManagementSystem
}

sig Customer {
	isPremium: one Bool,
	customerOrder: some Order //Ask composition
}


sig ManagementSystem {
	managementSystemEmployee: some Employee,
	managementSystemOrder: set Order,
	managementSystemAnalytics: one Analytics
}

sig Delivery {
	canBeDelivered: one Bool,
	deliveredEmployee: one Courier +  Intern,
	deliveryOrder: some Order,
	deliveryTime: one Time
} 

//TODO: Next order
sig Order {
	isDelivered: one Bool,
	orderCustomer: one Customer,
	orderPizza: some Pizza,
	orderChef: one Chef,
	nextOrder: lone Order, //TODO: Need to add acyclic constraint
	orderDelivery: one Delivery,
	orderManagementSystem: one ManagementSystem,
	orderTime: one Time
}

sig Time { }

sig Address {}

sig Payment { }

sig Pizza {
	isCooked: one Bool,
	isGourmet: one Bool,
	pizzaChef: set Chef, //Check that relation
	pizzaOrder: one Order
}


//Better reading: Add <: instead of relation names, refactor to Name <: NameName2 to model Name->Name2
fact SymmetricRelations {
	~(Order <: orderCustomer) = Customer <: customerOrder &&
	~(Order <: orderDelivery) = Delivery <: deliveryOrder &&
	~(Order <: orderManagementSystem) = ManagementSystem <: managementSystemOrder &&
	~(Order <: orderChef) = Chef <: chefOrder &&
	~(Pizza <: pizzaOrder) = Order <: orderPizza &&
	~(Pizza <: pizzaChef) = Chef <: chefPizza &&
	~(ManagementSystem <: managementSystemEmployee) = Employee <: employeeManagementSystem &&
	~(ManagementSystem <: managementSystemAnalytics) = Analytics <: analyticsManagementSystem &&
	~(Delivery <: deliveredEmployee) = (Intern <: internDelivery + Courier <: courierDelivery)  &&
	~(Manager <: managerAnalytics) = Analytics <: analyticsManager
}

//Number 3
fact ordersAtATime{
	all c: Customer | let dO = # getDeliveredOrders[c,False] | 
		c.isPremium = True => dO =< 2 else dO =< 1
}

//Number 4
fact gourmetPizza{
	all c: Customer | (True in c.customerOrder.orderPizza.isGourmet) => (c.isPremium = True)
}

//Number 5.1
fact orderNormalOrPremium{
	all o: Order | let 	
		numG = numberOfGourmet[o,True] ,
		numNotG = numberOfGourmet[o,False] |
		numG = 1 && numNotG = 0 || numG = 0 && numNotG <= 3 && numNotG >= 1

}

//Number 5.2, Ask for timeOrder relation. Would need to add to sig and to symm. fact
fact chefsHandleThreeMax{
	all t: Time, c: Chef | # (t.~orderTime & c.chefOrder) =< 3
}

//Number 5.3
fact internsHandleTwoMax{
	all t: Time, i: Intern | # (t.~deliveryTime & i.internDelivery) =< 2
}

//Number 6.1
fact deliveryUpToThreeOrders{
	all d: Delivery | # d.deliveryOrder <= 3
}

//TODO: Ask about constraint no. 6

//Number 7 
fact onlyCookedPizzasInDelivery{
	// p in Delivery.deliveryOrder.orderPizza
	all p:Pizza | (p.isCooked = False) =>  False in (p.pizzaOrder.orderDelivery.canBeDelivered)
}

//Number 8, TODO: Keep one connection: O1->O2->O3
fact noLoopsInNextOrder{
	all o :Order | o.nextOrder != o && not (o->o in ^nextOrder)
}


fun numberOfGourmet[o: Order, b: Bool]: Int{
	# (o.orderPizza <: isGourmet).b
}


/*
 * Predicates
 */

pred empty { }

pred notCooked[p: Pizza]{
	p.isCooked = False
}

pred notPremium[c: Customer] {
	c.isPremium = False
}

// True iff c is a premium customer.
pred isPremiumCustomer[c : Customer] {
	c.isPremium = True
}

// True iff p is a gourmet pizza.
pred isGourmetPizza[p : Pizza] {
	p.isGourmet = True
}

// True iff c is carrying more than a single order in a delivery d.
pred moreThanOneCourier[c: Courier] {  }

// True iff i is carrying more than a single order in a delivery d.
pred moreThanOneInternCourier[i: Intern] { }

// True iff c is cooking more than a single order 
pred moreThanOneChef[c: Chef] {  }

// True iff i is cooking more than a single order
pred moreThanOneInternCook[i: Intern] {  }

// True iff i is a piazza delivering intern
pred isDeliveringIntern[i : Intern] {  }

// True iff o1 is ordered before o2
pred orderIsBefore[o1, o2: Order] {  }

// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {  }


/*
 * Functions
 */

/*
// Returns all the orders which are being cooked by chef c
fun getAllOrders[c: Chef] : set Order {  }

// Returns all the orders which are being delivered by courier c
fun getAllOrdersFromCourier[c: Courier] : set Order {  }

// Returns all the orders which are being delivered by intern i
fun getAllOrdersFromInternDelivery[i: Intern] : set Order {  }

// Returns all the orders which are being cooked by intern i
fun getAllOrdersFromInternCooked[i: Intern] : set Order {  }

// Returns the start time of order o
fun getStart[o : Order] : Time {  }

// Returns the end time of order o
fun getEnd[o: Order] : Time {  }

// Returns the delivery address of order o
fun getDeliveryAddr[o: Order] : Address {  } 

// Returns the payment information of customer c
fun getPayment[c: Customer] : Payment {  } 

// Returns all the orders that are being cooked
fun getAllBeingCookedOrders[m: ManagementSystem] : set Order {  } 

*/

// Returns all the orders that are being delivered
fun getAllBeingDeliveredOrders[m: ManagementSystem] : set Order {
	(m.managementSystemOrder <: isDelivered).True
}

// Returns all the orders that are being delivered
fun getDeliveredOrders[c: Customer, b: Bool] : set Order {
	(c.customerOrder <: isDelivered).b
}


run notPremium for 3 but exactly 4 Pizza, exactly 1 Customer
run isPremiumCustomer for 3 but exactly 1 Customer, exactly 3 Order
run empty for 3 but exactly 1 Customer, exactly 1 Chef, exactly 1 Time, exactly 3 Order
run notCooked for 3 but 1 Delivery, exactly 1 Order, exactly 3 Pizza