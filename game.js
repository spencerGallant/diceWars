
// Constructor for area data, setting initial values for area properties
var AreaData = function(){
	this.size=0;		// The number of cells that make up this area
	this.cpos=0;		// The central cell of the area for drawing and logic purposes
	this.arm=0;			// The ID of the player/army that controls this area
	this.dice=0;		// The number of dice placed in this area, determining its strength
	
	// Variables to determine the center of the area for graphical representation
	this.left=0;
	this.right=0;
	this.top=0;
	this.bottom=0;
	this.cx=0;		// X coordinate of the center, derived from left and right
	this.cy=0;		// Y coordinate of the center, derived from top and bottom
	this.len_min=0;

	// Arrays for drawing the area's boundary lines
	this.line_cel = new Array(100);	// Cells that make up the boundary lines
	this.line_dir = new Array(100);	// Directions of the boundary lines
	this.join = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];	// Adjacency flags for other areas
}


// Constructor for player data, setting initial values for player properties
var PlayerData = function(){
	this.area_c=0;		// The count of areas controlled by the player
	this.area_tc=0;		// The count of the largest contiguous territory controlled
	this.dice_c=0;		// Total number of dice the player has across all areas
	this.dice_jun=0;	// Ranking of players based on the number of dice controlled
	this.stock=0;		// Number of dice in reserve for distribution during reinforcement
}

// Constructor for join data, defining directions to adjacent cells
var JoinData = function(){
	this.dir = [0,0,0,0,0,0]; // Directions to adjacent cells, aiding in movement and attack logic
}

// Constructor for history data, tracking actions and results for undo or replay functionality
var HistoryData = function(){
	this.from=0;	// ID of the attacking (or supplying) area
	this.to=0;		// ID of the defending area, 0 indicates a supply action
	this.res=0;		// Result of the action: 0 for failure, 1 for success
}

// Main game constructor function, initializing game state and logic
var Game = function(){
	// Player types array: null for human players, function references for AI players
	this.ai = [
		null, // First human player
		null, // Second human player
		ai_defensive, // AI player 1
		ai_defensive,
		ai_default,
		ai_default,
		ai_default
	];

	var i,j;

	// メソッド 隣のセル番号を返す (return the cell number to the next method)
	this.next_cel = function( opos, dir ){
		var ox = opos%this.XMAX;
		var oy = Math.floor(opos/this.XMAX);
		var f = oy%2;
		var ax=0;
		var ay=0;
		switch(dir){
			case 0: ax=f; ay=-1; break;	// 右上 (upper right)
			case 1: ax=1; break;	// 右 (right)
			case 2: ax=f; ay=1;break;	// 右下 (bottom right)
			case 3: ax=f-1; ay=1;break;	// 左下 (bottom left)
			case 4: ax=-1; break;	// 左 (left)
			case 5: ax=f-1; ay=-1; break;	// 左上 (upper left)
		}
		var x = ox+ax;
		var y = oy+ay;
		if( x<0 || y<0 || x>=this.XMAX || y>=this.YMAX ) return -1;
		return y*this.XMAX+x;
	}

	
	// Board dimensions and cell data initialization
	this.XMAX=28; // Board width in cells
	this.YMAX=32; // Board height in cells
	this.cel_max = this.XMAX * this.YMAX; // Total number of cells on the board
	this.cel = new Array(this.cel_max); // Array holding cell occupation data

	// Arrangement with adjacent cells
	this.join = new Array(this.cel_max);
	for( i=0; i<this.cel_max; i++ ){
		this.join[i] = new JoinData(); // Initialize join data for cell adjacency
		for( j=0; j<6; j++ ) this.join[i].dir[j] = this.next_cel(i,j); // Calculate adjacent cells
	}

	// Area data and map generation utilities
	this.AREA_MAX = 32;	// Maximum number of areas on the board
	this.adat = new Array(); // Array to hold area data
	for( i=0; i<32; i++ ) this.adat[i] = new AreaData(); // Initialize area data

	// Utilities for map creation and game state management
	this.num = new Array(this.cel_max);		// Array for area numbering
	for( i=0; i<this.cel_max; i++ ) this.num[i] = i; // Initialize area numbers
	this.rcel = new Array(this.cel_max);		// Adjacent cells for area expansion
	
	this.next_f = new Array(this.cel_max);	// Peripheral cell to use for penetration
	this.alist = new Array(this.AREA_MAX);	// Area list
	this.chk = new Array(this.AREA_MAX);	// For area drawing lines
	this.tc = new Array(this.AREA_MAX);		// Used in adjacent area number

	// Game state variables and player data
	this.pmax=7;		// Total number of players in the game
	this.user=0;		// Index of the human player
	this.user1=1;		// Index of the human player
	this.put_dice=3;	// Average number of dice allocated per area
	this.jun = [0,1,2,3,4,5,6,7];			// Player turn order
	this.ban = 0;			// Current player's turn index
	this.area_from=0;	// Source area for attack or movement
	this.area_to=0;		// Target area for attack
	this.defeat=0;		// Outcome of the last action: 0 for failure, 1 for success

	// player data
	this.player = new Array(8);
	this.STOCK_MAX=64;	// 最大ストック数 (maximum number of stocks)

	// Additional utilities for AI thinking, move history, and initial setup
	this.list_from = new Array(this.AREA_MAX*this.AREA_MAX);
	this.list_to = new Array(this.AREA_MAX*this.AREA_MAX);

	// Action history for undo or replay
	this.his = new Array(); 
	this.his_c = 0; // Counter for history entries

	// Initial placement
	this.his_arm = new Array(this.AREA_MAX); // Initial state of area ownership
	this.his_dice = new Array(this.AREA_MAX); // Initial state of dice distribution
	
	// Initializes and starts the game by setting up the game board, shuffling player order,
	// initializing player data, and preparing the game's history for tracking actions.
	this.start_game = function(){
		var i;
		// Shuffle player order to randomize game start. Each player is assigned a number (0-7),
    	// and this loop randomly rearranges those numbers to determine the playing order.
		for( i=0; i<8; i++ ) this.jun[i] = i;
		for( i=0; i<this.pmax; i++ ){
			var r = Math.floor(Math.random()*this.pmax);
			var tmp=this.jun[i]; this.jun[i]=this.jun[r]; this.jun[r]=tmp;
		}
		this.ban = 0; // Resets the turn counter, starting the game with the first player in the shuffled order.

		// Initialize player data for each player by creating a new instance of PlayerData.
    	// This includes setting up initial values like area count, dice count, etc.
		for( i=0; i<8; i++ ) this.player[i] = new PlayerData();

		// Calculate the largest contiguous territory (area_tc) for strategy purposes for each player.
		for( i=0; i<8; i++ ) this.set_area_tc(i);
		
		// Initialize the game's history tracking, which records each move's starting and ending points
    	// and whether the move was successful. This is useful for undo features or game analysis.
		this.his_c = 0;
		for( i=0; i<this.AREA_MAX; i++ ){
			this.his_arm[i] = this.adat[i].arm;
			this.his_dice[i] = this.adat[i].dice;
		}
	}
	
	// Calculates the largest contiguous territory controlled by a player (pn). This is important
	// for game strategies as controlling large contiguous areas might offer tactical advantages.
	this.set_area_tc = function( pn ){
		this.player[pn].area_tc = 0; // Reset the territory count for player pn.
		var i,j;
		// Initialize an array to check connections between areas to calculate the largest contiguous block.
		for( i=0; i<this.AREA_MAX; i++ ) this.chk[i] = i;

		// Loop through each area to find and merge contiguous territories for the player.
		while( 1 ){
			var f = 0;
			for( i=1; i<this.AREA_MAX; i++ ){
				if( this.adat[i].size == 0 ) continue;
				if( this.adat[i].arm != pn ) continue;
				for( j=1; j<this.AREA_MAX; j++ ){
					if( this.adat[j].size == 0 ) continue;
					if( this.adat[j].arm != pn ) continue;
					if( this.adat[i].join[j]==0 ) continue;
					if( this.chk[j] == this.chk[i] ) continue;
					if( this.chk[i] > this.chk[j] ) this.chk[i]=this.chk[j]; else this.chk[j]=this.chk[i];
					f = 1;
					break;
				}
				if( f ) break;
			}
			if( f==0 ) break;
		}

		// Count the size of each contiguous territory and find the largest.
		for( i=0; i<this.AREA_MAX; i++ ) this.tc[i]=0;
		for( i=1; i<this.AREA_MAX; i++ ){
			if( this.adat[i].size == 0 ) continue;
			if( this.adat[i].arm != pn ) continue;
			this.tc[this.chk[i]]++;
		}
		var max = 0;
		for( i=0; i<this.AREA_MAX; i++ ){
			if( this.tc[i] > max ){
				max = this.tc[i]; // Update max if a larger contiguous territory is found.
			}
		}
		this.player[pn].area_tc = max; // Set the player's largest contiguous territory size.
	}
	
	
	// Accesses the current player's index from the turn order array (this.jun)
    // using the current turn counter (this.ban) and returns it.
	this.get_pn = function(){
		return this.jun[this.ban];
	}

	// Makes the map for the game
	this.make_map = function(){
		var i,j,k,c,an;
		
		for( i=0; i<this.cel_max; i++ ){
			var r = Math.floor(Math.random()*this.cel_max);
			var tmp=this.num[i]; this.num[i]=this.num[r]; this.num[r]=tmp;
		}

		for( i=0; i<this.cel_max; i++ ){
			this.cel[i] = 0;
			this.rcel[i] = 0;
		}
		var an = 1;
		this.rcel[Math.floor(Math.random()*this.cel_max)] = 1;	// 最初のセル
		
		while( 1 ){
			var pos;
			var min = 9999;
			for( i=0; i<this.cel_max; i++ ){
				if( this.cel[i] > 0 ) continue;
				if( this.num[i] > min ) continue;
				if( this.rcel[i] == 0 ) continue;
				min = this.num[i];
				pos = i;
			}
			if( min == 9999 ) break;

			var ret = this.percolate( pos, 8, an );
			if( ret == 0 ) break;
			an++;
			if( an >= this.AREA_MAX ) break;
		}
		for( i=0; i<this.cel_max; i++ ){
			if( this.cel[i] > 0 ) continue;
			var pos;
			var f = 0;
			var a = 0;
			for( k=0; k<6; k++ ){
				var pos = this.join[i].dir[k];
				if( pos<0 ) continue;
				if( this.cel[pos] == 0 ) f=1; else a=this.cel[pos];
			}
			if( f==0 ) this.cel[i] = a;
		}
		for( i=0; i<this.AREA_MAX; i++ ) this.adat[i] = new AreaData();

		for( i=0; i<this.cel_max; i++ ){
			an = this.cel[i];
			if( an>0 ) this.adat[an].size++;
		}
		for( i=1; i<this.AREA_MAX; i++ ){
			if( this.adat[i].size <= 5 ) this.adat[i].size = 0;
		}
		for( i=0; i<this.cel_max; i++ ){
			an = this.cel[i];
			if( this.adat[an].size == 0 ) this.cel[i] = 0;
		}

		for( i=1; i<this.AREA_MAX; i++ ){
			this.adat[i].left = this.XMAX;
			this.adat[i].right = -1;
			this.adat[i].top = this.YMAX;
			this.adat[i].bottom = -1;
			this.adat[i].len_min = 9999;
		}
		c = 0;
		for( i=0; i<this.YMAX; i++ ){
			for( j=0; j<this.XMAX; j++ ){
				an = this.cel[c];
				if( an>0 ){
					if( j<this.adat[an].left ) this.adat[an].left = j;
					if( j>this.adat[an].right ) this.adat[an].right = j;
					if( i<this.adat[an].top ) this.adat[an].top = i;
					if( i>this.adat[an].bottom ) this.adat[an].bottom = i;
				}
				c++;
			}
		}
		for( i=1; i<this.AREA_MAX; i++ ){
			this.adat[i].cx = Math.floor(( this.adat[i].left + this.adat[i].right ) / 2);
			this.adat[i].cy = Math.floor(( this.adat[i].top + this.adat[i].bottom ) / 2);
		}
		c=0;
		var x,y,len;
		for( i=0; i<this.YMAX; i++ ){
			for( j=0; j<this.XMAX; j++ ){
				an = this.cel[c];
				if( an>0 ){
					x = this.adat[an].cx-j; if( x<0 ) x = -x;
					y = this.adat[an].cy-i; if( y<0 ) y = -y;
					len = x+y;
					var f=0;
					for( k=0; k<6; k++ ){
						var pos = this.join[c].dir[k];
						if( pos>0 ){
							var an2 = this.cel[pos];
							if( an2 != an ){
								f=1;
								this.adat[an].join[an2] = 1;
							}
						}
					}
					if( f ) len += 4;
					if( len < this.adat[an].len_min ){
						this.adat[an].len_min = len;
						this.adat[an].cpos = i*this.XMAX+j;
					}
				}
				c++;
			}
		}

		for( i=0; i<this.AREA_MAX; i++ ) this.adat[i].arm = -1;
		var arm=0;	// 属軍
		var alist = new Array(this.AREA_MAX);
		while( 1 ){
			var c = 0;
			for( i=1; i<this.AREA_MAX; i++ ){
				if( this.adat[i].size == 0 ) continue;
				if( this.adat[i].arm >= 0 ) continue;
				alist[c] = i;
				c++;
			}
			if( c==0 ) break;
			var an = alist[Math.floor(Math.random()%c)];
			this.adat[an].arm = arm;
			arm++; if( arm>=this.pmax ) arm=0;
		}
		for( i=0; i<this.AREA_MAX; i++ ) this.chk[i] = 0;
		for( i=0; i<this.cel_max; i++ ){
			var area = this.cel[i];
			if( area==0 ) continue;
			if( this.chk[area]>0 ) continue;
			for( var k=0; k<6; k++ ){
				if( this.chk[area]>0 ) break;
				var n = this.join[i].dir[k];
				if( n>=0 ){
					if(this.cel[n]!=area){
						this.set_area_line(i,k);
						this.chk[area]=1;
					}
				}
			}
		}
		var anum = 0;
		for( i=1; i<this.AREA_MAX; i++ ){
			if( this.adat[i].size > 0 ){
				anum++;
				this.adat[i].dice = 1;
			}
		}
		anum *= (this.put_dice-1);
		var p=0;	// player
		for( i=0; i<anum; i++ ){
			var list = new Array(this.AREA_MAX);
			var c = 0;
			for( j=1; j<this.AREA_MAX; j++ ){
				if( this.adat[j].size == 0 ) continue;
				if( this.adat[j].arm != p ) continue;
				if( this.adat[j].dice >= 8 ) continue;
				list[c] = j;
				c++;
			}
			if( c==0 ) break;
			var an = list[Math.floor(Math.random()*c)];
			this.adat[an].dice++;
			p++; if( p>=this.pmax ) p=0;
		}
		
	}

	// used for map generation
	this.percolate = function( pt, cmax, an ){
		if( cmax < 3 ) cmax = 3;

		var i,j,k;
		var opos = pt;

		for(i=0; i<this.cel_max; i++ ) this.next_f[i]=0; 

		var c = 0;	
		while( 1 ){
			this.cel[opos] = an;
			c++;
			// 周囲セル
			for( i=0; i<6; i++ ){
				var pos = this.join[opos].dir[i];
				if( pos<0 ) continue;
				this.next_f[pos] = 1;
			}

			var min = 9999;
			for( i=0; i<this.cel_max; i++ ){
				if( this.next_f[i] == 0 ) continue;
				if( this.cel[i] > 0 ) continue;	
				if( this.num[i] > min ) continue;	
				min = this.num[i];
				opos = i;
			}
			if( min == 9999 ) break;
			if( c>=cmax ) break;	
		}
		// 隣接セルを加える
		for( i=0; i<this.cel_max; i++ ){
			if( this.next_f[i] == 0 ) continue;
			if( this.cel[i] > 0 ) continue;		
			this.cel[i] = an;
			c++;
			for( k=0; k<6; k++ ){
				var pos = this.join[i].dir[k];
				if( pos<0 ) continue;
				this.rcel[pos] = 1;
			}
		}
		return c;
	}

	this.set_area_line = function( old_cel, old_dir ){
		var c = old_cel;
		var d = old_dir;
		var area = this.cel[c];	// エリア番号
		var cnt = 0;
		this.adat[area].line_cel[cnt] = c;
		this.adat[area].line_dir[cnt] = d;
		cnt++;
		for( var i=0; i<100; i++ ){
			d++; if( d>=6 ) d=0;
			var n = this.join[c].dir[d];
			if( n>=0 ){
				if( this.cel[n] == area ){
					c = n;
					d-=2; if( d<0 ) d+=6;
				}
			}
			this.adat[area].line_cel[cnt] = c;
			this.adat[area].line_dir[cnt] = d;
			cnt++;
			if( c==old_cel && d==old_dir ) break;
		}
	}

	this.com_thinking = function() {
		var ai_function = this.ai[ this.jun[this.ban] ]

		return ai_function(this);
	}

	this.set_his = function( from, to, res ){
		this.his[this.his_c] = new HistoryData();
		this.his[this.his_c].from = from;
		this.his[this.his_c].to = to;
		this.his[this.his_c].res = res;
		this.his_c++;
	}
}



