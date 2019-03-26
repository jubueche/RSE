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
	internDelivery: lone Delivery,
	internOrder: set Order
}


sig Chef extends Employee {
	chefOrder: set Order
}

sig Courier extends Employee {
	courierDelivery: one Delivery
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
	isDelivered: one Bool,
	deliveredEmployee: some Courier +  Intern,
	deliveryOrder: some Order
}

//TODO: Next order
sig Order {
	isCompleted: one Bool,
	isHead: one Bool,
	orderCustomer: one Customer,
	orderPizza: some Pizza,
	orderChef: lone Chef,
	orderIntern: lone Intern,
	nextOrder: lone Order,
	previousOrder: lone Order,
	orderDelivery: one Delivery,
	orderManagementSystem: one ManagementSystem,
	orderTime: one Time
}

fact pOrder{
	previousOrder = ~nextOrder
}

sig Time { 
	t: Int
}


sig Pizza {
	isCooked: one Bool,
	isGourmet: one Bool,
	pizzaOrder: one Order
}



//Better reading: Add <: instead of relation names, refactor to Name <: NameName2 to model Name->Name2
fact SymmetricRelations {
	~(Order <: orderCustomer) = Customer <: customerOrder &&
	~(Order <: orderDelivery) = Delivery <: deliveryOrder &&
	~(Order <: orderManagementSystem) = ManagementSystem <: managementSystemOrder &&
	~(Order <: orderChef) = Chef <: chefOrder &&
	~(Order <: orderIntern) = Intern <: internOrder &&
	~(Pizza <: pizzaOrder) = Order <: orderPizza &&
	~(ManagementSystem <: managementSystemEmployee) = Employee <: employeeManagementSystem &&
	~(ManagementSystem <: managementSystemAnalytics) = Analytics <: analyticsManagementSystem &&
	~(Delivery <: deliveredEmployee) = (Intern <: internDelivery + Courier <: courierDelivery)  &&
	~(Manager <: managerAnalytics) = Analytics <: analyticsManager
}

fact internNoDeliveryWhenChef{
	all i: Intern | True in i.isChef => # i.internDelivery = 0 &&
	False in i.isChef => # i.internOrder = 0
}

fact orderEitherByChefOrIntern{
	all o: Order | # (o.orderIntern + o.orderChef) <= 1
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

//Number 5.2
fact chefsHandleThreeMax{
	all c: Chef | # (c.chefOrder <: isCompleted.False) =< 3
}

//Number 5.3
fact internsHandleTwoMax{
	all i: Intern | # (i.internOrder <: isCompleted.False) =< 2
}

//Number 6.1
fact deliveryUpToThreeOrders{
	all d: Delivery | # d.deliveryOrder <= 3
}

//Number 6.2
fact deliveredByConstraint{
	all d: Delivery | let dI = # d.deliveredEmployee & Intern
					| let dC =  # d.deliveredEmployee & Courier
					| (dC = 0) => (dI = 0 || # dI = 2) && (dC = 1) => (dI <= 1)
}


//Number 7 
fact onlyCookedPizzasInDelivery{
	all p:Pizza | (p.isCooked = False) => (p.pizzaOrder.orderDelivery.canBeDelivered = False)
}

//Number 8   Head -> O1 -> O2 -> Tail
fact noLoopsInNextOrder{
	all o: Order | o.nextOrder != o && not (o->o in ^nextOrder) && (one o.~nextOrder || o.isHead=True)
}

fact oneHead{
	all o, o': Order | (o.isHead=True && o'.isHead=True) => o=o' 
}


fact handledIfPreceedingHandled{
	all o,o' :Order | (isHandled[o] && o' in o.^previousOrder) => isHandled[o']
}

pred isHandled[o:Order] {
	# (o.orderChef + o.orderIntern) > 0
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

// True iff c is carrying more than a single order in a delivery d. Correct since each Courier/Intern has only one delivery
pred moreThanOneCourier[c: Courier] {
	# c.courierDelivery.deliveryOrder > 1
}

// True iff i is carrying more than a single order in a delivery d.
pred moreThanOneInternCourier[i: Intern] {
	# i.internDelivery.deliveryOrder > 1
}

// True iff c is cooking more than a single uncompleted order
pred moreThanOneChef[c: Chef] {
	# (c.chefOrder <: isCompleted).False > 1
}

// True iff i is cooking more than a single order
pred moreThanOneInternCook[i: Intern] {
	# (i.internOrder <: isCompleted).False > 1
}

// True iff i is a piazza delivering intern
pred isDeliveringIntern[i : Intern] {
	i.isChef = False
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
/*fun getAllBeingDeliveredOrders[m: ManagementSystem] : set Order {
	(m.managementSystemOrder <: isDelivered).True
}*/

// Returns all the orders that are being delivered
fun getDeliveredOrders[c: Customer, b: Bool] : set Order {
	(c.customerOrder  <: orderDelivery.isDelivered).b
}


run notPremium for 3 but exactly 4 Pizza, exactly 1 Customer
run isPremiumCustomer for 4 but exactly 2 Customer, exactly 4 Order
run empty for 3 but exactly 1 Customer, exactly 1 Chef, exactly 1 Time, exactly 3 Order
run notCooked for 3 but 1 Delivery, exactly 1 Order, exactly 3 Pizza
run empty for 3