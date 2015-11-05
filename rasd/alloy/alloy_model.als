// Alloy model for myTaxiService system.

// Defines Bool, True, False
open util/boolean

// Dates are expressed as the number of seconds from 1970-01-01,
// because Alloy doesn't have date object and other signatures
// aren't comparable.

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
	logs: some TaxiLog,
	currentLog: some TaxiLog,
	numberOfSeats: one Int,
}{
	currentLog in logs
	no log: logs | log.date > currentLog.date

	one address
	one phoneNumber

	some licenseID
	some numberOfSeats
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
	beginDate: one Int,
	endDate: lone Int,
	taxiDriver: lone TaxiDriver,

	// passengers who booked a taxi
	registeredPassengers: some Passenger,

	// number of people in the taxi
	numOfTravellers: one Int,

	status: one RideStatus,
	isShared: one Bool,
	isReserved: one Bool,
	reservationDate: lone Int,
} {
	reservationDate < beginDate
	beginDate < endDate
	numOfTravellers <= taxiDriver.numberOfSeats
	#registeredPassengers <= numOfTravellers
	(#registeredPassengers > 1) implies (isShared = True)
	(#destination > 1) implies (isShared = True)
	#destination <= #registeredPassengers
}

sig TaxiLog {
	date: one Int,
	position: one Position,
	status: one TaxiStatus,
	taxiDriver: one TaxiDriver,
} {
	date > 0
	this in taxiDriver.logs
	no t: TaxiDriver | t != taxiDriver and this in t.logs
}

abstract sig TaxiStatus {}
one sig AVAILABLE extends TaxiStatus {}
one sig BUSY extends TaxiStatus {}
one sig OFFLINE extends TaxiStatus {}

abstract sig RideStatus {}
one sig RESERVED_NOT_ALLOCATED extends RideStatus {}
one sig WAITING extends RideStatus {}
one sig ON_BOARD extends RideStatus {}
one sig COMPLETED extends RideStatus {}

sig TaxiZone {
	number: one Int,
	queue: set TaxiDriver
} {
	number > 0
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
}

fact UniqueUsers {
	no u1, u2: User | (u1 != u2 and
		(u1.username = u2.username or u1.email = u2.email))
}

fact reservedButNotAllocatedRide{
	all r:Ride | (r.status=RESERVED_NOT_ALLOCATED
		implies
		(one beginDate and one r.origin and some r.destination
		and r.isReserved=True and no r.taxiDriver))
}

fact reservedAndAllocatedRide{
	all r:Ride | (r.status=WAITING and r.isReserved=True)
		 implies (one beginDate and one r.origin and one r.destination
		 and one r.taxiDriver )
}

fact waitingRide{
	all r: Ride | (r.status=WAITING
		 implies (one beginDate and one r.origin and one r.taxiDriver) )
}

fact beginningRide {
	// When the ride is started the beginDate is recorded
	all r: Ride| (r.status=ON_BOARD
		implies (one beginDate and one r.origin and one r.taxiDriver) )
}

fact endingRide {
	// When the ride ends the endDate is recorded
	all r: Ride | (r.status=COMPLETED
		implies (one beginDate and one endDate and one r.origin
		and one r.destination and one r.taxiDriver) )
}

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
	all p: Passenger, r1, r2: Ride |
		(p in r1.registeredPassengers
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
		<=> (some z: TaxiZone | t in z.queue)
}

// Each taxi driver must be inserted in at most one taxi queue.
fact OneQueuePerDriver {
	all t: TaxiDriver | (lone z: TaxiZone | t in z.queue)
}

// ---- ASSERTIONS ----


assert noTwoPassengersOnNoSharedTaxi{
	no r:Ride | (#r.registeredPassengers>1 and (r.isShared=False))
}
//check noTwoPassengersOnNoSharedTaxi
//OK


assert AllTaxiInQueue {
	all t: TaxiDriver | (lone z: TaxiZone | t in z.queue)
}
//check AllTaxiInQueue
//OK


assert noNewRideIfTaxiDriverOnRoad {
	all  r1, r2: Ride | (r1.taxiDriver=r2.taxiDriver and r1 != r2)
		implies
		(r1.endDate < r2.beginDate or r2.endDate < r1.beginDate)
}
//check noNewRideIfTaxiDriverOnRoad
//OK

assert noReservationInThePast{
	all r:Ride |
	(r.isReserved= True implies r.beginDate > r.reservationDate)
}

//check noReservationInThePast
//OK

assert reservingRide{
	all r:Ride| (r.status=WAITING and r.isReserved=True
		implies
		(one r.beginDate and one r.origin and one r.destination))
}

//check reservingRide
//OK

assert beginningRide{
	all r:Ride| (r.status=ON_BOARD
		implies (one beginDate and one r.origin))
}

//check beginningRide
//OK

assert endingRide{
	all r:Ride| (r.status=COMPLETED
		implies  (one beginDate and one endDate
		and one r.origin and one r.destination))
}
//check endingRide
//OK

// ---- PREDICATES ----

pred show(){
	#Passenger >= 2
	#Ride >= 1
	#TaxiDriver >= 2
	#TaxiLog >= 3
	#{x: Ride | x.isShared = True} >= 1
	#{t: TaxiZone | #t.queue >=1 } >= 1
	all p: Passenger | (some r: Ride | p in r.registeredPassengers)
}

run show for 10
