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
	isChef: one Bool,
	internDelivery: some Delivery,
	internOrder: set Order	
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

sig Order {
	isDelivered: one Bool,
	isHead: one Bool,
	orderCustomer: one Customer,
	orderPizza: some Pizza,
	orderChef: one Chef,
	orderIntern: one Intern,
	nextOrder: lone Order,
	orderDelivery: one Delivery,
	orderManagementSystem: one ManagementSystem,
	orderTime: one Time
}

sig Time {
	t: Int
}

sig Address {}

sig Payment { }

sig Pizza {
	isCooked: one Bool,
	isGourmet: one Bool,
	pizzaChef: set Chef, //Check that relation
	pizzaOrder: one Order
}


//TODO: Order can be made only by CHEF or INTERN, not by both
fact SymmetricRelations {
	~(Order <: orderCustomer) = Customer <: customerOrder &&
	~(Order <: orderDelivery) = Delivery <: deliveryOrder &&
	~(Order <: orderManagementSystem) = ManagementSystem <: managementSystemOrder &&
	~(Order <: orderChef) = Chef <: chefOrder &&
	//~(Order <: orderIntern) = Intern <: internOrder &&
	~(Pizza <: pizzaOrder) = Order <: orderPizza &&
	~(Pizza <: pizzaChef) = Chef <: chefPizza &&
	~(ManagementSystem <: managementSystemEmployee) = Employee <: employeeManagementSystem &&
	~(ManagementSystem <: managementSystemAnalytics) = Analytics <: analyticsManagementSystem &&
	~(Delivery <: deliveredEmployee) = (Intern <: internDelivery + Courier <: courierDelivery)  &&
	~(Manager <: managerAnalytics) = Analytics <: analyticsManager
}

/*
fact internNoDeliveryWhenChef{
	all i: Intern | True in i.isChef => # i.internDelivery = 0 &&
	False in i.isChef => # i.internOrder = 0
} */

/*
fact orderEitherByChefOrIntern{
	all o: Order | # o.orderIntern + o.orderChef = 1
}*/

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

/*
fact deliveredByTwoInternOrOneCourierOrOneInternAndOneCourier{
	all o: Order | ((# o.orderDelivery.~internDelivery = 1) => (#o.orderDelivery.~courierDelivery = 1)) ||
		((# o.orderDelivery.~internDelivery = 2) => (# o.orderDelivery.~courierDelivery = 0)) ||
		((# o.orderDelivery.~internDelivery = 0) => (# o.orderDelivery.~courierDelivery = 1))
}*/

//Number 7 
fact onlyCookedPizzasInDelivery{
	all p:Pizza | (p.isCooked = False) =>  False in (p.pizzaOrder.orderDelivery.canBeDelivered)
}

//Number 8, TODO: Check if correct
fact noLoopsInNextOrder{
	all o: Order | o.nextOrder != o && not (o->o in ^nextOrder) && (one o.~nextOrder || o.isHead=True)
}

fact oneHead{
	all o, o': Order | (o.isHead=True && o'.isHead=True) => o=o' 
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
pred moreThanOneCourier[c: Courier] {
	all d: Delivery | # d.(c.courierDelivery <: deliveryOrder) > 1
}

// True iff i is carrying more than a single order in a delivery d.
pred moreThanOneInternCourier[i: Intern] {
	all d: Delivery | # d.(i.internDelivery <: deliveryOrder) > 1
}

// True iff c is cooking more than a single order 
pred moreThanOneChef[c: Chef] {
	# c.chefOrder > 1
}

// True iff i is cooking more than a single order
pred moreThanOneInternCook[i: Intern] {
	# i.internOrder > 1
}

// True iff i is a pizza delivering intern
pred isDeliveringIntern[i : Intern] {
	False = i.isChef
}

// True iff o1 is ordered before o2
pred orderIsBefore[o1, o2: Order] {
	isBefore[o1.orderTime, o2.orderTime]
}

// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {
	t1.t < t2.t
}


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
run isPremiumCustomer for 4 but exactly 2 Customer, exactly 4 Order
run empty for 3 but exactly 1 Customer, exactly 1 Chef, exactly 1 Time, exactly 3 Order
run notCooked for 3 but exactly 1 Courier, 3 Order, 2 Delivery, exactly 0 Intern
run moreThanOneCourier for 3