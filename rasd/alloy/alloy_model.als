// Alloy model for myTaxiService system.

abstract sig User {
	nickname: one String,
	email: one String,
	password: one String,
}

sig Passenger extends User {

}

sig TaxiDriver extends User {
	licenseID: one Integer
}

// GPS position
sig Position {
	latitude: one Float,
	longitude: one Float,
}

// Signature representing a generic ride
sig Ride {
	startLocation: lone Position,
	endLocation: one Position,
	startTime: lone Date,
	taxiDriver: one TaxiDriver,
	passenger: some Passenger
}
