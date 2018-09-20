React is very popular these days.
And so are promises.

This leads to code such as this:
- one button : click on button : get results : update *something* to display the results
- another button : close dialog box

Now, the use may click (the resquest is sent), then close the dialog box (the request is received).

The result of the request may be quite important, but the dialog box has been closed. So what should be done ?
- Very ugly code does this : update unmounted commponent => error the development console
- Very fancy thing that is more difficult to do : display a notification when the dialog box has been closed, or possibly cancel the request, but this is usually not possible, or prevent the user from closing the dialog box

It is possible to trigger this behavior on such a giant thing as facebook : first create some content, then like it, then delete it and quickly click on the list of people who like the content => an error message occurs stating the action is not possible
