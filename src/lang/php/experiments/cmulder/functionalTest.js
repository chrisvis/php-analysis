var casper = require('casper').create({
    verbose: true,
    logLevel: "debug"
});

var path = casper.cli.args[0] || 'wordpress_current';
var url = 'http://arne.sen.cwi.nl:9999/' + path;

function open(path) {
	casper.thenOpen(url + path, function () {
		console.log('Location is ' + this.getCurrentUrl());
	});
}

casper.start(url, function () {
	this.test.assertTitle('Dynamic Test | Just another WordPress site');
	this.click("li.page-item-2 a");
});
	
casper.then(function() {
	this.test.assertSelectorHasText('h1.entry-title', 'Sample Page');
});

open("/?p=1");

casper.thenOpen(url + '/wp-login.php', function() {
	this.fill('form#loginform', {
		log: 'admin',
		pwd: 'jaapaap',
	}, true);
});

casper.then(function() {
	// NOOP
});

casper.then(function() {
    this.test.assertExists('#wpadminbar', 'Admin bar available, successfully logged');
});

open("/wp-admin/upload.php");

casper.then(function() {
	this.test.assertTextExists('Media Library');
	casper.capture("test.png");
	this.click(".media-icon a");

});

open("/wp-admin/themes.php?page=custom-header");
open("/wp-admin/widgets.php");
open("/wp-admin/nav-menus.php");
open("/wp-admin/edit.php");
open("/wp-admin/edit.php?post_type=page");
open("/wp-admin/edit-comments.php");
open("/wp-admin/options-writing.php");
open("/wp-admin/edit-tags.php?taxonomy=category");
open("/wp-admin/post-new.php");
open("/wp-admin/options-reading.php");
open("/wp-admin/plugins.php");
open("/wp-admin/plugin-install.php");

casper.then(function() {	
	this.click("#wp-admin-bar-logout a");
});

casper.then(function () {
	this.test.assertTextExists('You are now logged out', 'Succesfully logged out.');

})

casper.run(function() {
	this.test.renderResults(true);
});
