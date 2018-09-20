[REST](https://en.wikipedia.org/wiki/Representational_state_transfer)  (Representational State Transfer) defines recommandations for creating web services, and in particular binds various HTTP methods and paths to different operations.

The stated goals are to simplify the construction and use of webservices for managing resources.

The recommandations describes interaction with particular items and collections.

An item can be retrieved (GET), replaced (PUT), deleted (DELETE) or patched (PATCH).
At the collection level, the prescribed operations are
- get a list of items (URIs or ids) (GET)
- replace the whole collection with something else (PUT)
- create a new item in the collection (POST)
- delete the whole collection (DELETE)

Many RESTful services follow these guidelines, and often nothing more. Proponents of the RESTful approach are usually do not define what they mean by "REST", leaving other people to believe that REST is only this and nothing more.

When the service is done and running, the need for bulk operations, such as adding, retrieving, modifying or removing a list of hundreds or thousands of items, and the RESTful service require performing one HTTP request per item, which is not efficient.

=> REST should mandate recommandations with respect to bulk operations.

Another problem is that many objects are complex and made of parts, and only parts of these objects may be required at any time.

=> REST should mandate that when retrieving items, the fields of interest should be made part of the query.

As an example to this, the GitHub REST API for users only allows to list all GitHub users, with all their details for each of them, or to retrieve the details of only one user.
To get a representation of all the contributors of some project, this API requires makeing one query for each user, which is not efficient.