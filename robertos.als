// Bool signature used for boolean relations.
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
	customerOrder: some Order
}

sig ManagementSystem {
	managementSystemEmployee: some Employee,
	managementSystemOrder: set Order,
	managementSystemAnalytics: one Analytics
}

sig Delivery {
	canBeDelivered: one Bool,
	isDelivered: one Bool,
	deliveryEmployee: some Courier +  Intern,
	deliveryOrder: some Order
}

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
	startTime: one Time,
	endTime: one Time,
	orderPayment: one Payment,
	orderAddress: one Address
}

fact pOrder{
	previousOrder = ~nextOrder
}

sig Payment { }

sig Address { }

sig Time { 
	t: Int
}


sig Pizza {
	isCooked: one Bool,
	isGourmet: one Bool,
	pizzaOrder: one Order
}

// Enforces the fact that all relationships must be symmetric 
fact SymmetricRelations {
	~(Order <: orderCustomer) = Customer <: customerOrder &&
	~(Order <: orderDelivery) = Delivery <: deliveryOrder &&
	~(Order <: orderManagementSystem) = ManagementSystem <: managementSystemOrder &&
	~(Order <: orderChef) = Chef <: chefOrder &&
	~(Order <: orderIntern) = Intern <: internOrder &&
	~(Pizza <: pizzaOrder) = Order <: orderPizza &&
	~(ManagementSystem <: managementSystemEmployee) = Employee <: employeeManagementSystem &&
	~(ManagementSystem <: managementSystemAnalytics) = Analytics <: analyticsManagementSystem &&
	~(Delivery <: deliveryEmployee) = (Intern <: internDelivery + Courier <: courierDelivery)  &&
	~(Manager <: managerAnalytics) = Analytics <: analyticsManager
}

// Enfornces the fact that an intern if is a chef (isCooking = True) it cannot also be an intern. 
fact internNoDeliveryWhenChef{
	all i: Intern | True in i.isChef => # i.internDelivery = 0 &&
	False in i.isChef => # i.internOrder = 0
}

fact orderEitherByChefOrIntern{
	all o: Order | # (o.orderIntern + o.orderChef) <= 1
}

/*
 *  Facts for TASK 3-8.
 */ 

// Number 3
fact ordersAtATime{
	all c: Customer | let dO = # getDeliveredOrders[c,False] | 
		c.isPremium = True => dO =< 2 else dO =< 1
}

// Number 4
fact gourmetPizza{
	all c: Customer | (True in c.customerOrder.orderPizza.isGourmet) => (c.isPremium = True)
}

// Number 5.1
fact orderNormalOrPremium{
	all o: Order | let 	
		numG = numberOfGourmet[o,True] ,
		numNotG = numberOfGourmet[o,False] |
		numG = 1 && numNotG = 0 || numG = 0 && numNotG <= 3 && numNotG >= 1

}

// Number 5.2
fact chefsHandleThreeMax{
	all c: Chef | # (c.chefOrder <: isCompleted.False) =< 3
}

// Number 5.3
fact internsHandleTwoMax{
	all i: Intern | # (i.internOrder <: isCompleted.False) =< 2
}

// Number 6.1
fact deliveryUpToThreeOrders{
	all d: Delivery | # d.deliveryOrder <= 3
}

//Number 6.2
fact deliveredByConstraint{
	all d: Delivery | let dI = # d.deliveryEmployee & Intern
					| let dC =  # d.deliveryEmployee & Courier
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


/*
 * Predicates used for testing 
 */

pred empty { }

pred isHandled[o:Order] {
	# (o.orderChef + o.orderIntern) > 0
}

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
	isBefore[o1.startTime, o2.startTime]
}

// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {
	t1.t < t2.t
}


/*
 * Functions
 */

fun numberOfGourmet[o: Order, b: Bool]: Int{
	# (o.orderPizza <: isGourmet).b
}

// Returns all the orders which are being cooked by chef c
fun getAllOrders[c: Chef] : set Order {
	(c.chefOrder <: orderPizza.isCooked).False
}

// Returns all the orders which are being delivered by courier c
fun getAllOrdersFromCourier[c: Courier] : set Order {
	(c.courierDelivery.deliveryOrder <: orderDelivery.isDelivered).False
}

// Returns all the orders which are being delivered by intern i
fun getAllOrdersFromInternDelivery[i: Intern] : set Order {
	(i.internDelivery.deliveryOrder <: orderDelivery.isDelivered).False
}

// Returns all the orders which are being cooked by intern i
fun getAllOrdersFromInternCooked[i: Intern] : set Order {
	(i.internOrder <: orderPizza.isCooked).False
}

// Returns the start time of order o
fun getStart[o : Order] : Time {
	o.startTime
}

// Returns the end time of order o
fun getEnd[o: Order] : Time {
	o.endTime
}

// Returns the delivery address of order o
fun getDeliveryAddr[o: Order] : Address {
	o.orderAddress
} 

// Returns the payment information of customer c
fun getPayment[c: Customer] : Payment {
	c.customerOrder.orderPayment
} 

// Returns all the orders that are being cooked
fun getAllBeingCookedOrders[m: ManagementSystem] : set Order {
	(m.managementSystemOrder <: orderPizza.isCooked).False
} 


// Returns all the orders that are being delivered
fun getAllBeingDeliveredOrders[m: ManagementSystem] : set Order {
	(m.managementSystemOrder <: orderDelivery.deliveryEmployee).Employee - (m.managementSystemOrder  <: orderDelivery.isDelivered).True
}

// Returns all the orders that are being delivered
fun getDeliveredOrders[c: Customer, b: Bool] : set Order {
	(c.customerOrder  <: orderDelivery.isDelivered).b
}


run empty for 3 but exactly 4 Chef, exactly 3 Courier, exactly 1 Manager, exactly 2 Intern, exactly 1 ManagementSystem