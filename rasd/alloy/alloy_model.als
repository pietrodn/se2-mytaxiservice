// Alloy model for myTaxiService system.

abstract sig User {
	username: one String,
	email: one String,
	password: one String,
	name: one String,
	surname: one String,
	address: lone String,
	phoneNumber: lone String,
	emailConfirmed: one Boolean,
} {
	no u1, u1: User | (u1 != u2 and
		(u1.username = u2.username or u1.email = u2.email))
}

sig Passenger extends User {
	currentPosition: lone Position,
}

sig TaxiDriver extends User {
	licenseID: one Integer,
	taxiNumberPlate: one String,
	address: one String,
	phoneNumber: one String,
	logs: set TaxiLog,
	currentLog: one TaxiLog,
}{
	currentLog in logs
	no log: logs | log.date > currentLog.date

	no u1, u1: TaxiDriver | (u1 != u2 and
		(u1.licenseID = u2.licenseID
			or u1.taxiNumberPlate = u2.taxiNumberPlate))
}

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
	destination: one Position,
	beginDate: lone Date,
	endDate: lone Date,
	taxiDriver: one TaxiDriver,
	passengers: some Passenger,
	status: one RideStatus,
} {
	beginDate < endDate
}

sig TaxiLog {
	date: one Date,
	position: one Position,
	status: one TaxiStatus,
} {
	// There should not be two taxi log for the same taxi driver in the same date.
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
	number: one Integer,
	queue: one TaxiQueue
}{
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
	all p: Passenger, r1, r2: Ride | (p in r1.passengers
		and p in r2.passengers and r1 != r2)
		implies
		(r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}

// Two rides for the same taxi driver must not overlap.
fact OneConcurrentRidePerDriver {
	all t: TaxiDriver, r1, r2: Ride | (t = r1.taxiDriver
		and p = r2.taxiDriver and r1 != r2)
		implies
		(r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}

// If the taxi driver is available,
// he must be inserted in at least a taxi queue.
fact AvailableDriverInSomeQueue {
	all t: TaxiDriver | (t.currentLog.status = AVAILABLE)
		<=> (some q: TaxiQueue | t in q.drivers)
}

// Each taxi driver must be inserted in at most one taxi queue.
fact OneQueuePerDriver {
	all t: TaxiDriver | (lone q: TaxiQueue | t in q)
}
