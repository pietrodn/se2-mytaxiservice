// Alloy model for myTaxiService system.

// Defines Bool, True, False
open util/boolean

// Dates are expressed as the number of seconds from 1970-01-01

abstract sig User {
	username: one String,
	email: one String,
	password: one String,
	name: one String,
	surname: one String,
	address: lone String,
	phoneNumber: lone String,
	emailConfirmed: one Bool,
}

fact UniqueUsers {
	no u1, u2: User | (u1 != u2 and
		(u1.username = u2.username or u1.email = u2.email))
}

sig Passenger extends User {
	currentPosition: lone Position,
}

sig TaxiDriver extends User {
	licenseID: one Int,
	taxiNumberPlate: one String,
	logs: set TaxiLog,
	currentLog: lone TaxiLog,
	numberOfSeats: one Int,
}{
	currentLog in logs
	no log: logs | log.date > currentLog.date

	#address = 1
	#phoneNumber = 1
}

fact UniqueTaxiDrivers {
	no u1, u2: TaxiDriver | (u1 != u2 and
		(u1.licenseID = u2.licenseID
			or u1.taxiNumberPlate = u2.taxiNumberPlate))
}

// GPS position
sig Position {
	latitude: one Int,
	longitude: one Int,
}

// Signature representing a generic ride
// (from when the taxi driver accepts the call
// until he leaves the passenger on destination).
sig Ride {
	origin: lone Position,
	destination: some Position,
	beginDate: lone Int,
	endDate: lone Int,
	taxiDriver: one TaxiDriver,
	
	// passengers who booked a taxi
	registeredPassengers: some Passenger,

	// number of people in the taxi
	numOfTravelers: one Int,

	status: one RideStatus,
	isShared: one Bool,
} {
	beginDate < endDate
	numOfTravelers <= taxiDriver.numberOfSeats
	#registeredPassengers<=numOfTravelers
	(#registeredPassengers > 1) implies (isShared = True)
	(#destination > 1) implies (isShared = True)
	#destination <= #registeredPassengers
}

sig TaxiLog {
	date: one Int,
	position: one Position,
	status: one TaxiStatus,
}

fact UniqueTaxiLog {
	// There should not be two taxi logs
	// for the same taxi driver in the same date.
	no tl1, tl2: TaxiLog, td: TaxiDriver |
		tl1 in td.logs and tl2 in td.logs
		and tl1.date = tl2.date and tl1 != tl2
}

abstract sig TaxiStatus {}
sig AVAILABLE extends TaxiStatus {}
sig BUSY extends TaxiStatus {}
sig OFFLINE extends TaxiStatus {}

abstract sig RideStatus {}
sig WAITING extends RideStatus {}
sig ON_BOARD extends RideStatus {}
sig COMPLETED extends RideStatus {}

sig TaxiZone {
	number: one Int,
	queue: one TaxiQueue
}

fact UniqueTaxiZone {
	no z1, z2: TaxiZone | z1 != z2 and z1.number = z2.number
	queue = ~zone
}

sig TaxiQueue {
	zone: one TaxiZone,
	drivers: set TaxiDriver,
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

assert A {
	all t: TaxiDriver | (lone q: TaxiQueue | t in q.drivers)
}

check A for 3
