@api @MongoDB
Feature: Save to mongo
	saveToMongo should dump a stream to a mongoDB backend

	Background:
		Given I drop every existing stream
		Given I connect to 'Mongo' cluster at '${MONGO_HOST}'

	@ignore @tillfixed(DECISION-299)
	Scenario: Saving from an unexistent stream
		When I start saving to MongoDB a stream with name 'unexistantStream'
		Then an exception 'IS' thrown with class 'StratioEngineOperationException' and message like 'Stream .* does not exist'

	Scenario: Saving from an nice existent stream
		When I create a stream with name 'mongoSaveStream' and columns (with type):
			| 1  | String  |
			| 2  | Integer |
		When I start saving to MongoDB a stream with name 'mongoSaveStream'
		Then the stream 'mongoSaveStream' has 'SAVE_TO_MONGO' as active actions
		And I insert into a stream with name 'mongoSaveStream' this data:
			| 1 | a |
			| 2 | 4 |
		And I wait '30' seconds
		Then an exception 'IS NOT' thrown
		And a Mongo dataBase 'stratio_decision' contains a table 'mongoSaveStream' with values:
			| 1-String | 2-Integer |
			| a        | 4         |
		And I drop a MongoDB database 'stratio_decision'

	@ignore @tillfixed(DECISION-300)
	Scenario Outline: Saving from an nice existent stream, with unnacepted mongo fields
		When I create a stream with name 'mongobadColsSaveStream' and columns (with type):
			| <columnName>  | String  |
		When I start saving to MongoDB a stream with name 'mongobadColsSaveStream'
		And I insert into a stream with name 'mongobadColsSaveStream' this data:
			| <columnName> | a |
		And I wait '30' seconds
		Then an exception 'IS NOT' thrown
		And a Mongo dataBase 'stratio_decision' doesnt contains a table 'mongobadColsSaveStream'

		Examples:
		| columnName |
		| a.value    |
		| a$value    |

	@ignore @tillfixed(DECISION-299)
	Scenario Outline: Saving unnacepted streams at Mongo
		When I create a stream with name '<streamName>' and columns (with type):
			| 1  | String  |
			| 2  | Integer |
		When I start saving to MongoDB a stream with name '<streamName>'
		Then an exception 'IS' thrown with class 'StratioAPISecurityException' and message like '<message>'

		Examples:
		| streamName        | message                     |
		|                   | Stream name cannot be empty  |
		| //NULL//          | Stream name cannot be null  |
		| $tream            | Stream name $tream is not compatible with |
		| system.stream     | Stream name system.stream is not compatible with |
		| sostem.stream     | Stream name sostem.stream is not compatible with |