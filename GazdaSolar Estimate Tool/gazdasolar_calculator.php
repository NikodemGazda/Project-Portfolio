/**
 * Plugin Name: GazdaSolar Calculator Plugin
 * Description: Calculates the estimated cost and number of panels based on user input.
 * Version: 1.0
 * Author: Nikodem Gazda
 */

// Add the shortcode for the calculator form
add_shortcode('gazdasolar_calculator', 'gazdasolar_calculator_shortcode');

// Constants
const FEES = 5; // added fees for gazdasolar to profit, in percent of installation cost
const PANEL_COST = 140; // in $
const POWER_PER_PANEL = 75; // in KWh / month
const NO_FINANCING_YEARS = 20; // asssumption for savings calculation when not financing

function gazdasolar_calculator_shortcode() {
    ob_start(); // Start output buffering

    //rates for each zip code
	$zipcode_LUT = array(
		34653 => 0.1317,
		34652 => 0.2317,
		34690 => 0.3317,
		34691 => 0.4317,
		34655 => 0.5317
	);
	
	// Initialize variables
    $number_of_panels = 0;
    $estimated_cost = 0;
	$zipcode = 0;
	$savings = 0;
	$financing_flag = false;
	$financing_length = 7; // in years
	$financing_cost = 0;
	$financing_savings = 0;
	$state = 0;

    // Handle form submission
    if (isset($_POST['submit'])) {
        // Retrieve user inputs
        $electricity_cost = floatval($_POST['electricity_cost']);
        $electricity_usage = floatval($_POST['electricity_usage']);
		$zipcode = floatval($_POST['zipcode']);
		$financing_flag = isset($_POST['financing_flag']) ? true : false;
		$financing_length = isset($_POST['financing_length']) ? intval($_POST['financing_length']) : 0;
		
		// choose which side to use
		if ( $electricity_usage==0 && $electricity_cost==0 && $zipcode==0) {
			// state change
			$state = 0;
		// zipcode wrong or not in range
		} else if ($zipcode!=0 && !isset($zipcode_LUT[$zipcode])) {
			$state = 3;
		// using electricity usage to calculate results
		} else if ($electricity_usage!=0 && $zipcode!=0) {
			//state change
			$state = 0;
			
			// Perform calculations
			// estimating cost based on zip code (used later for financing)
			if ($electricity_cost == 0) {
				$electricity_cost = $electricity_usage * $zipcode_LUT[$zipcode];
			}
			$number_of_panels = $electricity_usage / POWER_PER_PANEL;
			$estimated_cost = $number_of_panels * PANEL_COST * FEES;
		// using electricity cost to calculate results
		} else if ($electricity_cost!=0 && $zipcode!=0) {
			//state change
			$state = 0;
			
			// Perform calculations
			// estimating usage based on zip code
			if ($electricity_usage == 0) {
				$electricity_usage = $electricity_cost / $zipcode_LUT[$zipcode];
			}
			$number_of_panels = $electricity_usage / POWER_PER_PANEL;
			$estimated_cost = $number_of_panels * PANEL_COST * FEES;
		} else if ($zipcode == 0){
			// state change
			$state = 1;
		} else if ($electricity_cost == 0 && $electricity_usage==0 && $zipcode!=0) {
			// state change
			$state = 2;
		}
		
		//adjusting details
		if ($financing_flag) {
			if ($financing_length == 7) {
				$estimated_cost *= 1.10;
			} else if ($financing_length == 12) {
				$estimated_cost *= 1.05;
			} else if ($financing_length == 15) {
				$estimated_cost *= 1.04;
			} else if ($financing_length == 25) {
				$estimated_cost *= 1.02;
			}
			$savings = $electricity_cost*12*$financing_length-$estimated_cost;
			$financing_cost = $estimated_cost/(12*$financing_length);
			$financing_savings = $savings/(12*$financing_length);
		} else {
			$savings = $electricity_cost*12*NO_FINANCING_YEARS - $estimated_cost;
		}
    }

    // Display the calculator form
    ?>
    <style>
		.calculator-form {
			background-color: #1dae70;
			box-shadow: 0 0 15px rgba(0, 0, 0, 0.75);
			border-radius: 30px;
			padding: 15px;
			margin-bottom: 20px;
		}

		.calculator-form h2 {
			color: #15261c;
			margin-top: 0;
			text-align: center;
			margin-bottom: 20px;
		}
		
		.calculator-form h3 {
			color: #15261c;
			font-size: 180%; 
			margin-top: 0;
			text-align: center;
			margin-bottom: 20px;
		}

		.calculator-form label {
			display: block;
			margin-bottom: 10px;
		}

		.calculator-form input[type="number"],
		.calculator-form input[type="submit"] {
			padding: 5px;
			margin-bottom: 10px;
			text-align: right;
			width: 65%;
		}

		.calculator-inputs {
			display: flex;
			justify-content: space-between;
			align-items: center;
			margin-bottom: 20px;
			margin: auto;
		}

		.calculator-inputs-left,
		.calculator-inputs-right {
			flex-basis: 42%;
			box-shadow: 0 0 15px rgba(0, 0, 0, 0.5);
			padding: 10px;
			background-color: #ffffff;
			border-radius: 10px;
			text-align: center;

		}

		.or-container {
			flex-basis: 6%;
			text-align: center;
		}
		
		.calculator-inputs-bottom {
			background-color: #ffffff;
			box-shadow: 0 0 15px rgba(0, 0, 0, 0.5);
			border-radius: 10px;
			padding: 10px;
			margin-top: 12px;
/* 			margin-left: 40px;
			margin-right: 40px; */
		}
		
		.calculator-inputs-bottom-list {
			display: flex;
			justify-content: space-between;
			align-items: center;
			padding-left: 80px;
			padding-right: 80px;
		}
		
		.calculator-inputs-bottom-list input {
			flex-basis: 40%;
		}

		.calculate-button-container input[type="submit"] {
			width: 100%;
			background-color: #f6d804;
			box-shadow: 0 0 15px rgba(0, 0, 0, 0.5);
			color: #15261c;
			text-align: center;
			margin-top: 12px;
			margin-bottom: 12px;
			padding: 7px;
			font-size: 150%;
		}
		
		.calculator-results {
			background-color: #ffffff;
			box-shadow: 0 0 15px rgba(0, 0, 0, 0.5);
			border-radius: 10px;
			padding: 10px;
		}
		
		.results-header {
			display: flex;
			justify-content: space-between;
			align-items: center;
			padding-left: 10px;
			padding-right: 10px;
		}
		
		.details-container {
		  	display: flex;
			align-items: center;
			justify-content: center;
			padding-left: 10px;
			padding-right: 10px;
		}
		
		.details-bars {
			background-color: #a1a1a1;
			flex-grow: 1;
			height: 1px;
			margin-left: 25px;
			margin-right: 25px;
			margin-bottom: 18px;
			border-radius: 10px;
		}
		
		.detail-values {
			display: flex;
			justify-content: space-between;
			align-items: center;
			padding-left: 80px;
			padding-right: 80px;
		}
		
		.detail-values h2 {
			color:#1dae70;
			font-size: 35px;
			text-align: right;
			flex-basis: 50%;
			text-shadow: 0 0 3px rgba(0, 0, 0, 0),
						 0 0 3px rgba(0, 0, 0, 0),
						 0 0 3px rgba(0, 0, 0, 0),
						 0 0 3px rgba(0, 0, 0, 0);
		}
		
		.detail-values h3 {
			text-align: left;
			font-size: 25px;
			flex-basis: 50%;
		}
		
	</style>

	<div class="calculator-form">
		<h2>Free Estimate Tool</h2>
		<form method="post" action="">
			<div class="calculator-inputs">
				<div class="calculator-inputs-left">
					<label for="electricity_cost">Monthly Electricity Cost:</label>
					<span style="margin-bottom: 10px; padding: 5px">$</span>
					<input type="number" name="electricity_cost" id="electricity_cost" value="<?php echo isset($_POST['electricity_cost']) ? $_POST['electricity_cost'] : ''; ?>" placeholder="e.g. 1000">
				</div>
				
				<div class="or-container">
					<h3>OR</h3>
				</div>
				
				<div class="calculator-inputs-right">
					<label for="electricity_usage">Monthly Electricity Usage:</label>
					<input type="number" name="electricity_usage" id="electricity_usage" value="<?php echo isset($_POST['electricity_usage']) ? $_POST['electricity_usage'] : ''; ?>" placeholder="e.g. 1000">
					<span style="margin-bottom: 10px; margin-left: 10px;">KWh</span>
				</div>				
			</div>
			<div class="calculator-inputs-bottom">
				<div class="calculator-inputs-bottom-list">
					<label for="zipcode">Zipcode:</label>
					<input type="number" name="zipcode" id="zipcode" value="<?php echo isset($_POST['zipcode']) ? $_POST['zipcode'] : ''; ?>" placeholder="e.g. 34653">
				</div>
				<div class="calculator-inputs-bottom-list">
					<label for="financing_flag">Financing?</label>
					<input type="checkbox" name="financing_flag" id="financing_flag" style="margin-bottom: 10px;" <?php echo isset($_POST['financing_flag']) ? 'checked' : ''; ?>>
				</div>
				<div class="calculator-inputs-bottom-list">
					<label for="financing_length">Financing Length:</label>
					<select name="financing_length" id="financing_length">
				<option value="7" <?php echo isset($_POST['financing_length']) && $_POST['financing_length'] == '7' ? 'selected' : ''; ?>>7 years</option>
				<option value="12" <?php echo isset($_POST['financing_length']) && $_POST['financing_length'] == '12' ? 'selected' : ''; ?>>12 years</option>
				<option value="15" <?php echo isset($_POST['financing_length']) && $_POST['financing_length'] == '15' ? 'selected' : ''; ?>>15 years</option>
				<option value="25" <?php echo isset($_POST['financing_length']) && $_POST['financing_length'] == '25' ? 'selected' : ''; ?>>25 years</option>
					</select>
				</div>
			</div>
			<div class="calculate-button-container">
				<input type="submit" name="submit" value="Calculate">
			</div>
		</form>

		<div class="calculator-results">
			<?php if ($state == 0): ?>
				<div class="results-header">
					<h2 style="padding-top: 20px; font-size: 28px">Estimated System Cost: </h2>
					<h1 style="color:#1dae70;	
							   text-shadow: 0 0 2px rgba(0, 0, 0, 0),
										    0 0 2px rgba(0, 0, 0, 0),
										    0 0 2px rgba(0, 0, 0, 0),
										    0 0 2px rgba(0, 0, 0, 0),
										    0 0 2px rgba(0, 0, 0, 0),
										    0 0 2px rgba(0, 0, 0, 0),
										    0 0 2px rgba(0, 0, 0, 0);
								margin-bottom: 0px; font-size: 40px;">$<?php echo number_format($estimated_cost/1000,1); ?>k</h1>
				</div>
				<div class="details-container">
					<div class="details-bars"></div>
				  	<h6 style="color: #a1a1a1;">DETAILS</h6>
					<div class="details-bars"></div>
				</div>
				<div class="detail-values">
					<h3>Estimated Savings:</h3>
					<h2>$<?php echo number_format($savings/1000,1); ?>k</h2>
				</div>
				<?php if ($financing_flag == true): ?>
					<div class="detail-values">
						<h3>Estimated Monthly Cost with Financing:</h3>
						<h2>$<?php echo number_format($financing_cost,1); ?></h2>
					</div>
					<div class="detail-values">
						<h3>Estimated Monthly Savings with Financing:</h3>
						<h2>$<?php echo number_format($financing_savings,1); ?></h2>
					</div>
				<?php endif; ?>
			<?php elseif ($state == 1): ?>
				<h3 style="margin-top: 20px">Please add Zipcode</h3>
			<?php elseif ($state == 2): ?>
				<h3 style="margin-top: 20px">Please fill Monthly Electricity Cost or Monthly Electricity Usage</h3>
			<?php elseif ($state == 3): ?>
				<h3 style="margin-top: 20px">Unfortunately, your property is out of range of our services or the zipcode is incorrect.</h3>
			<?php else: ?>
				<h3 style="margin-top: 20px">Total System Cost: ---</h3>
			<?php endif; ?>
		</div>
	</div>

<?php

	return ob_get_clean(); // Return the buffer contents
}
