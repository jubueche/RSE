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
	management: ManagementSystem
}

sig Intern extends Employee {
	delivers: some Delivery,
	isChef: one Bool
} {
//delivers.deliveredBy = Intern
}


sig Chef extends Employee {
	processOrder: set Order,
	makes: some Pizza //Check that relation
}

sig Courier extends Employee {
	delivers: some Delivery
}

one sig Manager {
	analyses: one Analytics
}

sig Analytics {
	managedByAnalytics: one Manager,
	managedByManagementSystem: one ManagementSystem
}

sig Customer {
	isPremium: one Bool,
	customerOrders: some Order //Ask composition
} 

//Better reading: Add <: instead of relation names
fact SymmetricRelations {
	~(Order <: orderedBy) = Customer <: customerOrders &&
	~partOfDelivery = deliveryOrders &&
	~deliveredBy = (Intern <: delivers + Courier <: delivers)  &&
	~partOf = contains &&
	~managedBy = manageOrders &&
	~processedBy = processOrder &&
	~madeBy = makes &&
	~manageEmployees = management &&
	~manageAnalytics = managedByManagementSystem &&
	~analyses = managedByAnalytics
}


sig ManagementSystem {
	manageEmployees: some Employee,
	manageOrders: set Order,
	manageAnalytics: one Analytics
}

sig Delivery {
	deliveredBy: one Courier +  Intern,
	deliveryOrders: some Order
} 

sig Order {
	orderedBy: one Customer,
	contains: some Pizza,
	processedBy: one Chef,
	nextOrder: lone Order, //TODO: Need to add acyclic constraint
	partOfDelivery: one Delivery,
	managedBy: one ManagementSystem,
	delivered: one Bool
}

sig Time { }

sig Address {}

sig Payment { }

sig Pizza {
madeBy: set Chef, //Check that relation
isGourmet: one Bool,
partOf: one Order
}


/*
 * Predicates
 */

pred empty { }

// True iff c is a premium customer.
pred isPremiumCustomer[c : Customer] { }

// True iff p is a gourmet pizza.
pred isGourmetPizza[p : Pizza] {  }

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

// Returns all the orders that are being delivered
fun getAllBeingDeliveredOrders[m: ManagementSystem] : set Order {  } 

*/

run empty for 3 but exactly 4 Order, exactly 4 Pizza, 2 Analytics
