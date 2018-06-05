

function GVis() {
	/*************** Setting up the variables  ************/
	var self = this;
	//Set the width and height variables to be the height and width of the browser
	this.width = window.innerWidth;
	this.height = window.innerHeight*0.9;
	
	// Hardcode some URI's to pass to the query
	this.sub = "https://datachemist.net/ipg/candidate/osoba_ipg9663419";
	this.share = "https://datachemist.net/ipg/candidate/osoba_ipg11704456";
	this.bank = "https://datachemist.net/ipg/candidate/osoba_ipg10030806";
	// Instantiate a form to hold the seed URIs 
	this.initial_data_form = new FormData();
	// Instantiate basegraph
	this.baseNodes
	this.baseLinks;
	// Instantiate display graph
	this.nodes;
	this.links;
	// Instantiate svg element 
	this.svg;
	
	this.minDate = 0 // Jan 1st, 1970
	this.maxDate = 1525261230 // nowish
	this.currentDate = 1525261230 // nowish
	
	// Append an svg object to the body with dims from above ^^
	this.svg = d3.select("#vis").append("svg").attr("width", this.width).attr("height", this.height);

	/********* Setup/Instantiate Graph Elements+Simulation **********/
	
	// Individual links, nodes and text graphical elements
	this.linkElements;
	this.nodeElements;
	this.textElements;
	// Append graphic element to svg which are groups for graph elements
	this.linkGroup = this.svg.append("g").classed("links", true);
	this.nodeGroup = this.svg.append("g").classed("nodes", true);
	this.textGroup = this.svg.append("g").classed("texts", true);
	// Var for selecting and deselecting elem when clicked twice
	this.selected_id;
	
	// INITIALISE FORCES AND SIMULATION
	this.linkForce = d3.forceLink()
		.distance(50)
		.id(function(link){return link.id});
	//  .strength(link => link.strength)
	
	// create the force object 
	this.simulation  = d3.forceSimulation()
		.force('link', this.linkForce)
		.velocityDecay(.6)
		.force('charge', d3.forceManyBody().strength(function(x,y){
			if(self.nodeVisibility(x,self) == 'hidden' ||
			   self.nodeVisibility(x,self) == 'hidden'){
				return 0;
			}else{
				return -5;
			}
		}))
		.force('center', d3.forceCenter(this.width/2, this.height/2));
		//.size([this.width,this.height]);

	// node drag 
	this.drag_drop = d3.drag()
		.on('start', function(node) {
			node.fx = node.x
			node.fy = node.y
		})
		.on('drag', function(node) {
			self.simulation.alphaTarget(0.7).restart()
			node.fx = d3.event.x
			node.fy = d3.event.y
		})
		.on('end', function(node) {
			if (!d3.event.active) {
				self.simulation.alphaTarget(0)
			}
			node.fx = null
			node.fx = null
		});
}
/****************** Graph functionality ******************/


// increase repulsion
GVis.prototype.increase_repulsion = function(graph_node){
	var self = this;
	this.simulation.force("charge", d3.forceManyBody().strength(function(x, y){
		if(self.nodeVisibility(x,self) == 'hidden' || self.nodeVisibility(x,self) == 'hidden'){
			return 0;
		}else if (graph_node.id === x.id){
			return -80;			
		}else {
			return -30;
		}
	}));
	
	this.simulation.force("link").distance(function(x){
		if (x.target.id == graph_node.id || x.source.id == graph_node.id){
			return 100;
		} else {
			return 40;
		}
	});
	// could also do something with the link strength which makes the target
	// distance occur quickly (slightly reductive explanation)
	this.simulation.alphaTarget(0.7).restart();
}				 

// recentre graph
GVis.prototype.recentre = function(graph_node) {
	// get the x and y you need to transform the nodes by 
	var dcx = (window.innerWidth/2-graph_node.x);
	var dcy = (window.innerHeight/2-graph_node.y);
	//zoom.translate([dcx,dcy]); If we do zooming we'll need to do something here
	this.nodeElements.attr("transform", "translate("+ dcx + "," + dcy  + ")");
	this.linkElements.attr("transform", "translate("+ dcx + "," + dcy  + ")");
	//textElements.attr("transform", "translate("+ dcx + "," + dcy  + ")");
}

	
// node selection stuff 
GVis.prototype.highlightSelection = function(selectedNode){
	// get the neighbours of the node 
	var neighbours = this.getNeighbours(selectedNode);
	var self = this;
	// if the node is already selected remove highlighting
	if (this.selected_id === selectedNode.id){
		this.nodeElements.classed('highlighted', false);
		this.linkElements.classed('highlighted', false);
		//textElements.classed('highlighted', false);
	} else {
		// modify the nodes to highlight those selected
		this.nodeElements
			.classed('highlighted', function(node){ return neighbours.indexOf(node.id) !== -1});
		this.linkElements
			.classed('highlighted', function(link){ return self.isNeighbourLink(selectedNode, link)});
		//textElements
		//	.classed('highlighted', function(node){ return neighbours.indexOf(node.id) !== -1});
	}
}

//HERE WE HIGHLIGHT THE NODE AND DISPLAY SOME CONTEXTUAL INFORMATION 
GVis.prototype.select_node = function(selected_node) {
	// if the node is already highlighted we have to unhighlight
	this.highlightSelection(selected_node);
	//console.log(selected_node);
	// get the relevant context information
	var context = "<b>Node type: </b>" + selected_node.group + " <b>Uri:</b> " + selected_node.id;
	// if the same node was already selected
	if (this.selected_id === selected_node.id){
		// set the selection to null
		this.selected_id = null;
		// and remove the text from the box 
		jQuery(".context-div").html("");
	} else {
		// else set the selected id to the current node and add the context
		this.selected_id = selected_node.id
		//document.getElementById("context-div").innerHTML = context;	  
		jQuery(".context-div").html(context);
	}
}

// wrapper function to centre the graph and increase repulsion on immediate neightbours
GVis.prototype.centre_repulse = function(graph_node){
	this.recentre(graph_node);
	this.increase_repulsion(graph_node);
	this.select_node(graph_node);
}

GVis.prototype.follow_node = function(selected_node) {
	// Set the selected id to the current node 	this.selected_id = selected_node.id;
	// Boolean - retrieve whether you want to keep the current nodes
	var append_nodes = jQuery('#append-nodes').prop('checked');
	// instantiate a new form to send this to the API
	clicked_node = new FormData();
	clicked_node.append('id', this.selected_id);
	var self = this;
	// Get a graph fragment started from the selected node
	jQuery.ajax({
		url:'http://195.201.12.87:6161/dqs/dqs_get_frag',
		data: clicked_node,
		processData: false,
		contentType: false,
		type:'POST',
		success:function(response_data){
			self.update_data(response_data, append_nodes);
			self.update_simulation();
		}
	});
}

/*************** Helper Functions *************************/

GVis.prototype.getNeighbours = function(node) {
	return this.links.reduce(
		function(neighbours, link) {
			if (link.target.id === node.id) {
				neighbours.push(link.source.id);
			}else if (link.source.id === node.id) {
				neighbours.push(link.target.id)
			}
			return neighbours;
		}, [node.id]);
}

GVis.prototype.isNeighbourLink = function(node, link) { return link.target.id === node.id || link.source.id === node.id;  }


GVis.prototype.getNodesInRectangle = function(rect) {
	
	var r_atts = rect.getCurrentAttributes();
	// get the relevant x and y coordinates from the rectangle
	var x1 = r_atts.x1, x2 = r_atts.x2;
	var y1 = r_atts.y1, y2 = r_atts.y2;
	//
	var bounded_nodes = [];
	// Cycle through each of the current nodes and see if it is contained within the rectangle
	this.nodeElements.select(function(node, idx){
		// if the box is drawn from left to right
		if ((node.x > x1 && node.x < x2) && (node.y > y1 && node.y < y2) ||
			// or if the box is drawn right to left
			(node.x < x1 && node.x >  x2) && (node.y < y1 && node.y > y2)){
			bounded_nodes.push(node);
		}
	});
	return bounded_nodes;
}

GVis.prototype.getLinksInRectangle = function(bounded_nodes) {

	var node_ids = this.get_ids(bounded_nodes);
	var keep_links = [];
	
	this.linkElements.select(function(link) {
		// if the source and target of the link is in the bounded nodes return the link
		if(node_ids.indexOf(link.target.id) >= 0 && node_ids.indexOf(link.source.id) >= 0){
			keep_links.push(link);
		}
	});
	return keep_links;
}

/*************** Graph and Data Updates and Elements ********************/
// reset the nodes and links data
GVis.prototype.reset_data = function() {
	this.links = this.baseLinks.concat();
	this.nodes = this.baseNodes.concat();

	this.nodes.forEach(function (node){
		if(node.dateRange){
			if(!this.minDate || node.dateRange.fromDate && node.dateRange.fromDate.data < this.minDate){
				
				this.minDate = node.dateRange.fromDate.data;
			}
			if(!this.maxDate || node.dateRange.toDate && node.dateRange.toDate.data > this.maxDate){
				this.maxDate = node.dateRange.toDate.data;
			}
		}
	});
	
	this.selected_id = null;
}
// return the ids from the nodes 
GVis.prototype.get_ids = function(input_nodes){
	var ids = [];
	for(var i = 0; i < input_nodes.length; i++){
		ids[i] = input_nodes[i].id;
	}
	return ids;
}

// build the arrow add marker to links.
GVis.prototype.marker = function(color) {
	var reference;
	this.svg.append("svg:defs").selectAll("marker")
		.data([reference])
		.enter().append("svg:marker")
		.attr("id", String)
		.attr("viewBox", "0 -5 10 10")
		.attr("refX", 40)  // This sets how far back it sits, kinda
		.attr("refY", 0)
		.attr("markerWidth", 9)
		.attr("markerHeight", 9)
		.attr("orient", "auto")
		.attr("markerUnits", "userSpaceOnUse")
		.append("svg:path")
		.attr("d", "M0,-5L10,0L0,5")
		.style("fill", color);
	return "url(#" + reference + ")";
}

GVis.prototype.update_data = function(new_data, append_nodes) {

	if (append_nodes){
		// get the ids of the current and the new nodes
		current_node_ids = this.get_ids(this.nodes);
		new_node_ids = this.get_ids(new_data.nodes);
		// check if any of the new node ids are already in the graph
		node_keep_ids = new_node_ids.filter(function(id) { return current_node_ids.indexOf(id) === -1});
		// get rid of any duplicate nodess
		new_nodes = new_data.nodes.filter(function (node) {
			if (node_keep_ids.indexOf(node.id) >= 0){ 
				return node;
			}
		});
		// concatenate the new nodes and links
		this.nodes = this.nodes.concat(new_nodes);
		this.links = this.links.concat(new_data.links);
	} else {
		// Completely reset the data
		this.nodes = new_data.nodes.concat()
		this.links = new_data.links.concat()
	}
}

GVis.prototype.update_graph = function(log_nodes) {
	var self = this;

	if (log_nodes){
		console.log('tst');
		console.log(this.nodes);
		console.dir(this);
	}
	// update NODES ***		  
	this.nodeElements = this.nodeGroup.selectAll("circle")
		.data(this.nodes, function(node) { return node.id});
	// remove old nodes
	this.nodeElements.exit().remove();

	// wrapper function so I can pass the top level object
	var select_node_wrapper = function(graph_node){
		self.centre_repulse(graph_node, self);
	}
	var follow_node_wrapper = function(graph_node){
		self.follow_node(graph_node, self);
	}
	// enter and create new ones
	var node_enter = this.nodeElements
		.enter().append("circle")
		.attr('r', 10)
		.call(this.drag_drop)
		.on('click', select_node_wrapper)
		.on('dblclick', follow_node_wrapper);
	node_enter.append("title").text(function(d){ return d.name;});
	//node_enter.attr('id',function(d){ return d.id;});
	// merge new and old nodes	
	this.nodeElements = node_enter.merge(this.nodeElements)
		.style("visibility",function(n){ return self.nodeVisibility(n,self); });

	// update LINKS ***
	this.linkElements = this.linkGroup.selectAll("line")
		.data(this.links, function(link) {
			return link.target.id + link.source.id;
		});
	
	// remove old links
	this.linkElements.exit().remove();
	// enter and create new ones
	var linkEnter = this.linkElements
		.enter().append("line")
		.attr("stroke-width", function(link) { return Math.sqrt(link.value); })
		.attr("marker-end", this.marker("#999"));
	// merge new and old links 
	this.linkElements = linkEnter.merge(this.linkElements);
	this.linkElements =	this.linkElements
		.style("visibility",
			   function(l){ console.log(l); return self.linkVisibility(l,self); });
		
	// update TEXTELEMENTS ***		  
	/*textElements  = textGroup.selectAll("text")
		.data(nodes, function(node) { return node.id});
	// remove old texts
	textElements.exit().remove();
	// enter and create new ones
	var textEnter = textElements
		.enter().append("text")
		.text(node => node.name)
		.attr('font-size', 9)
		.attr('dx', 15)
		.attr('dy', 4);
	// merge new and old texts 
	textElements = textEnter.merge(textElements);
	*/
}

GVis.prototype.nodeVisibility = function(node,self){
	console.log(self.currentDate);
	if(node.dateRange){ 
		if(!node.dateRange.fromDate){
			if(!node.dateRange.toDate ||
			   node.dateRange.toDate.data > self.currentDate){
				return 'visible';
			}else{				
				return 'hidden';				
			}
		}else if(!node.dateRange.toDate){
			if (!node.dateRange.fromDate ||
				node.dateRange.fromDate.data < self.currentDate){
				return 'visible';
			}else{
				return 'hidden';
			}
		}else if(node.dateRange.fromDate.data < self.currentDate  &&
				 node.dateRange.toDate.data > self.currentDate){
			return 'visible';
		}else{
			return 'hidden';
		}
	}else{
		// no date range is considered transhistorical
		return 'visible';
	}
}

GVis.prototype.linkVisibility = function(link,self){
	/// Not sure who is responsible for this type polymorphism but it sucks. 
	var sourceid = link.source.id ? link.source.id : link.source;
	var targetid = link.target.id ? link.target.id : link.target;

	var source = self.nodes.find(node => node.id==sourceid);	
	var target = self.nodes.find(node => node.id==targetid);
	
	if( source && target ){
		var sourceVis = self.nodeVisibility(source,self);
		var targetVis = self.nodeVisibility(target,self);

		if(sourceVis == 'visible' && targetVis == 'visible'){
			return 'visible';
		}else{
			return 'hidden';
		}
	}else{
		// hopefully it's ok not to show our faces if the nodes don't exist.
		return 'hidden';
	}
}

GVis.prototype.update_simulation = function() {
	this.update_graph();
	this.simulation.nodes(this.nodes).on('tick', () => {
		this.nodeElements
			.attr("cx", node => node.x)
			.attr("cy", node => node.y)
		this.linkElements
			.attr('x1', link => link.source.x)
			.attr('y1', link => link.source.y)
			.attr('x2', link => link.target.x)
			.attr('y2', link => link.target.y)
		//textElements
		//	.attr("x", node => node.x)
		//	.attr("y", node => node.y)
	});
	this.simulation.force('link').links(this.links);
	this.simulation.alphaTarget(0.7).restart();
}


/**************** Square Drawing Stuff ****************/

function SelectionRectangle(graph) {
	this.element = null;
	this.previousElement = null;
	this.svg = graph.svg;
	this.graph = graph;
	this.currentY = 0;
	this.currentX = 0;
	this.originX = 0;
	this.originY = 0;
}

SelectionRectangle.prototype.setElement = function(ele) {
	this.previousElement = this.element;
	this.element = ele;
}
SelectionRectangle.prototype.getNewAttributes = function() {
	var x = this.currentX < this.originX ? this.currentX : this.originX;
	var y = this.currentY < this.originY ? this.currentY : this.originY;
	var width = Math.abs(this.currentX - this.originX);
	var height = Math.abs(this.currentY - this.originY);
	return {
	    x       : x,
	    y       : y,
	    width  	: width,
	    height  : height
	};
}	
SelectionRectangle.prototype.getCurrentAttributes = function() {
	// use plus sign to convert string into number
	var x = +this.element.attr("x");
	var y = +this.element.attr("y");
	var width = +this.element.attr("width");
	var height = +this.element.attr("height");
	return {
		x1  : x,
	    y1	: y,
	    x2  : x + width,
	    y2  : y + height
	};
}
SelectionRectangle.prototype.getCurrentAttributesAsText = function() {
	var attrs = this.getCurrentAttributes();
	return "x1: " + attrs.x1 + " x2: " + attrs.x2 + " y1: " + attrs.y1 + " y2: " + attrs.y2;
}

SelectionRectangle.prototype.init = function(newX, newY) {
	var rectElement = this.svg.append("rect")
		.attr("rx", 4)
		.attr("ry", 4)
		.attr("x", 0)
		.attr("y", 0)
		.attr("width", 0)
		.attr("height", 0)
		.classed("selection", true);
	this.setElement(rectElement);
	this.originX = newX;
	this.originY = newY;
	this.update(newX, newY);
}
SelectionRectangle.prototype.update = function(newX, newY) {
	this.currentX = newX;
	this.currentY = newY;
	var newAtts = this.getNewAttributes();
	this.element
		.attr("x", newAtts.x)
		.attr("y", newAtts.y)
		.attr("width", newAtts.width)
		.attr("height", newAtts.height)		
	
}
SelectionRectangle.prototype.focus = function() {
	// This if checks if there is actually any nodes in the graph
	var self = this.graph;
	
	if (jQuery("circle").length > 0){
		keep_nodes = this.graph.getNodesInRectangle(this);
		keep_links = this.graph.getLinksInRectangle(keep_nodes);
		if (keep_nodes.length === 0){
			alert("No nodes selected" );
		} else {
			
			this.graph.nodes = keep_nodes;
			this.graph.links = keep_links;
			this.graph.update_simulation();
		}
	} else {
		alert("Cannot select nodes. Please seed the graph.");
	}
}
SelectionRectangle.prototype.remove = function() {
    this.element.remove();
    this.element = null;
}
SelectionRectangle.prototype.removePrevious = function() {
    if(this.previousElement) {
    	this.previousElement.remove();
    }
}


SelectionRectangle.prototype.dragStart = function() {
	// this svg_elem thing is to get around not being able to
	// pass 'this' to d3.mouse
	var svg_elem = this.svg._groups[0][0]
	var p = d3.mouse(svg_elem);
	this.init(p[0], p[1]);
	this.removePrevious();
}

SelectionRectangle.prototype.dragMove = function() {
	// this svg_elem thing is to get around not being able to
	// pass 'this' to d3.mouse
	var svg_elem = this.svg._groups[0][0]
	var p = d3.mouse(svg_elem);
    this.update(p[0], p[1]);
	//attributesText.text(selectionRect.getCurrentAttributesAsText());
}

SelectionRectangle.prototype.dragEnd = function() {
	var finalAttributes = this.getCurrentAttributes();

	if(finalAttributes.x2 - finalAttributes.x1 > 1 && finalAttributes.y2 - finalAttributes.y1 > 1){
		// range selected
		d3.event.sourceEvent.preventDefault();
		// call the focus function to process what the square has selected 
		this.focus();
		// remove the square
		this.remove();
		
	} else { // This is left over from tutorial code see if we need it 
	    // single point selected and just remove the square
        this.remove();
	}	   
}

SelectionRectangle.prototype.initDragBehavior = function() {
	var self = this;

	var dragStartWrap = function(){
		self.dragStart(self);
	}
	var dragMoveWrap = function(){
		self.dragMove(self);
	}
	var dragEndWrap = function(){
		self.dragEnd(self);
	}
	self.svg.call(d3.drag()
				  .on("drag", dragMoveWrap)
				  .on("start", dragStartWrap)
				  .on("end", dragEndWrap)
				 );
}

function startGraph() {

	graphThing = new GVis();
	/********************* Seed the data **************************/
	
	// onclick calls canned queries in dacura and returns a json object to start graph  
	jQuery(".query").click(function(){
		
		graphThing.initial_data_form = new FormData();
		
		var uri;
		if (this.id == "sub") {
			uri = graphThing.sub;
		}
		else if (this.id == "share") {
			uri = graphThing.share;
		}
		else if (this.id == "bank") {
			uri = graphThing.bank;
		}

		var query_string = this.id + " " + uri; 
		
		graphThing.initial_data_form.append('query', query_string);
		//alert(graphThing.initial_data_form);
		console.log(graphThing.initial_data_form); 
		
		$.ajax({
			url: DcogJsClient.dqsServer,
			data: graphThing.initial_data_form,
			processData: false,
			contentType: false,
			type:'POST',
			success:function(response_data){
				// check if the inital state of the graph has been set
				graphThing.baseNodes = response_data.nodes;
				graphThing.baseLinks = response_data.links;
				// reset the data and update the simulation
				graphThing.reset_data();
				graphThing.update_simulation();
				// reset the Form
				graphThing.initial_data_form = new FormData();		
			}
		});  
	});

	// Buttons to stop the graph moving
	jQuery(function(){
		jQuery('#stop').click(function(){
			graphThing.simulation.stop();
		});
	});
	selectionRect = new SelectionRectangle(graphThing);
	selectionRect.initDragBehavior();


	/***************** Date Slider *************************/
	jQuery(function () {
		
		jQuery("#slider").slider({
			min: graphThing.minDate,
			max: graphThing.maxDate,
			change: function(event, ui) {
				var date = new Date(ui.value * 1000).toISOString();
				jQuery("#slide-val").text("Date: " + date);
				graphThing.currentDate = ui.value;
				graphThing.update_graph();
			}
		});
	});



	// Site specific configuration
}


jQuery(function() {
	jQuery.getScript("config.js", function(){
		startGraph();
	});	
});
/*
var clickTime = d3.select("#clicktime");
var attributesText = d3.select("#attributestext");

function clicked() {
	var d = new Date();
    clickTime
    	.text("Clicked at " + d.toTimeString().substr(0,8) + ":" + d.getMilliseconds());
}*/
// set the colour of the graphic
//var color = d3.scaleOrdinal(d3.schemeCategory20);  
/*.call(d3.zoom().on("zoom", function () {
             svg.attr("transform", d3.event.transform)
 }))*/
//  .force("link", d3.forceLink().distance(100).id(function(d) { return d.id; }))
