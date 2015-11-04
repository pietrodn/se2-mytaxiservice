// Alloy model for myTaxiService system.

// Defines Bool, True, False
open util/boolean

// Dates are expressed as the number of seconds from 1970-01-01

// ---- SIGNATURES ----

abstract sig User {
	username: one Stringa,
	email: one Stringa,
	password: one Stringa,
	name: one Stringa,
	surname: one Stringa,
	address: lone Stringa,
	phoneNumber: lone Stringa,
	emailConfirmed: one Bool,
}

sig Stringa {}

sig Passenger extends User {
	currentPosition: lone Position,
}

sig TaxiDriver extends User {
	licenseID: one Int,
	taxiNumberPlate: one Stringa,
	logs: set TaxiLog,
	currentLog: lone TaxiLog,
	numberOfSeats: one Int,
}{
	currentLog in logs
	no log: logs | log.date > currentLog.date

	#address = 1
	#phoneNumber = 1

	licenseID > 0
	numberOfSeats > 0
}

sig Float {}

// GPS position
sig Position {
	latitude: one Float,
	longitude: one Float,
}

// Signature representing a generic ride
// (from when the taxi driver accepts the call
// until he leaves the passenger on destination).
sig Ride {
	origin: lone Position,
	destination: some Position,
	beginDate: lone Int,
	endDate: lone Int,
	taxiDriver: lone TaxiDriver,

	// passengers who booked a taxi
	registeredPassengers: some Passenger,

	// number of people in the taxi
	numOfTravelers: one Int,

	status: one RideStatus,
	isShared: one Bool,
	isReserved: one Bool,
	reservationDate: lone Int,
} {
	beginDate > 0
	reservationDate > 0
	reservationDate< beginDate
	beginDate < endDate
	numOfTravelers <= taxiDriver.numberOfSeats
	#registeredPassengers <= numOfTravelers
	(#registeredPassengers > 1) implies (isShared = True)
	(#destination > 1) implies (isShared = True)
	#destination <= #registeredPassengers
	#taxiDriver <=1
}


sig TaxiLog {
	date: one Int,
	position: one Position,
	status: one TaxiStatus,
} {
	date > 0
}

abstract sig TaxiStatus {}
sig AVAILABLE extends TaxiStatus {}
sig BUSY extends TaxiStatus {}
sig OFFLINE extends TaxiStatus {}

abstract sig RideStatus {}
sig RESERVED_NOT_ALLOCATED extends RideStatus {}
sig WAITING extends RideStatus {}
sig ON_BOARD extends RideStatus {}
sig COMPLETED extends RideStatus {}

sig TaxiZone {
	number: one Int,
	queue: one TaxiQueue
} {
	number > 0
}

sig TaxiQueue {
	zone: one TaxiZone,
	drivers: set TaxiDriver,
}

// ---- FACTS ----

fact UniqueTaxiDrivers {
	no u1, u2: TaxiDriver | (u1 != u2 and
		(u1.licenseID = u2.licenseID
			or u1.taxiNumberPlate = u2.taxiNumberPlate))
}

fact UniqueTaxiLog {
	// There should not be two taxi logs
	// for the same taxi driver in the same date.
	no tl1, tl2: TaxiLog, td: TaxiDriver |
		tl1 in td.logs and tl2 in td.logs
		and tl1.date = tl2.date and tl1 != tl2
}

fact UniqueTaxiZone {
	no z1, z2: TaxiZone | z1 != z2 and z1.number = z2.number
	queue = ~zone
}

fact UniqueUsers {
	no u1, u2: User | (u1 != u2 and
		(u1.username = u2.username or u1.email = u2.email))
}


fact reservedButNotAllocatedRide{
all r:Ride| (r.status=RESERVED_NOT_ALLOCATED
 implies (#beginDate=1 and #r.origin=1 and #r.destination>=1 and r.isReserved=True))
}

fact reservedAndAllocatedRide{
all r:Ride| (r.status=WAITING and r.isReserved=True)
 implies (#beginDate=1 and #r.origin=1 and #r.destination>=1 and #r.taxiDriver=1 )
}

fact waitingRide{
all r:Ride| (r.status=WAITING
 implies (#beginDate=1 and #r.origin=1 and #r.taxiDriver=1) )
}

//If the ride is prenoted there must be a beginDate

fact beginningRide{
all r:Ride| (r.status=ON_BOARD
 implies (#beginDate=1 and #r.origin=1 and #r.taxiDriver=1) )
}
//When the ride is started the beginDate is recorded

fact endingRide{
all r:Ride| (r.status=COMPLETED 
 implies (#beginDate=1 and #endDate=1 and #r.origin=1
 and #r.destination>=1 and #r.taxiDriver=1) )
}
//When the ride ends the endDate is recorded




// If a taxi driver participates is a ride,
// he should be busy for the entire duration of the ride.
fact BusyDuringRide {
	all t: TaxiDriver, r: Ride, log: TaxiLog |
		(r.taxiDriver = t and log in t.logs
		and r.beginDate <= log.date and r.endDate >= log.date)
		implies
		(log.status = BUSY)
}

// Two rides for the same passenger must not overlap.
fact OneConcurrentRidePerPassenger {
	all p: Passenger, r1, r2: Ride | (p in r1.registeredPassengers
		and p in r2.registeredPassengers and r1 != r2)
		implies
		(r1.endDate < r2.beginDate or r2.endDate < r1.beginDate)
}

// Two rides for the same taxi driver must not overlap.
fact OneConcurrentRidePerDriver {
	all t: TaxiDriver, r1, r2: Ride | (t = r1.taxiDriver
		and t = r2.taxiDriver and r1 != r2)
		implies
		(r1.endDate < r2.beginDate or r2.endDate < r1.beginDate)
}

// If the taxi driver is available,
// he must be inserted in at least a taxi queue.
fact AvailableDriverInSomeQueue {
	all t: TaxiDriver | (t.currentLog.status = AVAILABLE)
		<=> (some q: TaxiQueue | t in q.drivers)
}

// Each taxi driver must be inserted in at most one taxi queue.
fact OneQueuePerDriver {
	all t: TaxiDriver | (lone q: TaxiQueue | t in q.drivers)
}

// ---- ASSERTIONS ----


assert noTwoPassengersOnNoSharedTaxi{
	no r:Ride | (#r.registeredPassengers>1 and (r.isShared=False))
}	
//check  noTwoPassengersOnNoSharedTaxi
//OK


assert AllTaxiInQueue {
	all t: TaxiDriver | (lone q: TaxiQueue | t in q.drivers)
}
//check  AllTaxiInQueue
//OK


assert noNewRideIfTaxiDriverOnRoad {
	all  r1, r2: Ride | (r1.taxiDriver=r2.taxiDriver and r1 != r2)
		implies
		(r1.endDate < r2.beginDate or r2.endDate < r1.beginDate)
}
//check  noNewRideIfTaxiDriverOnRoad
//OK

assert noPrenotationInThePast{
all r:Ride|( r.isReserved= True implies r.beginDate > r.reservationDate)
}

//check  noPrenotationInThePast
//OK

assert prenotingRide{
all r:Ride| (r.status=WAITING and r.isReserved=True
 implies 
 (#r.beginDate=1 and #r.origin=1 and #r.destination>=1))
}

//check  prenotingRide
//OK

assert beginningRide{
all r:Ride| (r.status=ON_BOARD implies (#beginDate=1 and #r.origin=1))
}

//check beginningRide
//OK

assert endingRide{
all r:Ride| (r.status=COMPLETED implies  (#beginDate=1 and #endDate=1
 and #r.origin=1 and #r.destination>=1))
}
//check endingRide
//OK

// ---- PREDICATES ----

pred show(){
	#Passenger > 1
	#Ride > 1
	#TaxiDriver > 1
	#Position > 1
	#{x: Ride | x.isShared = True} > 1
}

run show for 4
