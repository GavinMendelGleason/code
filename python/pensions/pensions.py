#!/usr/bin/env python

labour_force = 2195600
not_in_labour_force = 1459300
annual_average_industrial_wage = 37253

contribution = .20

participation_rate =  0.95

all_schemes = 733027

annual_total = annual_average_industrial_wage * (labour_force - all_schemes) * contribution * participation_rate

labour_capital_ratio = .5

number_of_workers = (annual_total * labour_capital_ratio) / annual_average_industrial_wage

target_jobs = 80000

## Job Seekers (2016)

total_job_seekers = 268726.0
live_register_cost_estimate = 4468297000.0
annual_live_register_pay = live_register_cost_estimate * 1.0 / total_job_seekers
pay_fraction = (annual_average_industrial_wage - annual_live_register_pay) * 1.0 / annual_average_industrial_wage

fraction_from_live_register = .5
target_job_cost = target_jobs * (1 - fraction_from_live_register + fraction_from_live_register * pay_fraction) * annual_average_industrial_wage / labour_capital_ratio

employable = annual_total * labour_capital_ratio / (((1 - fraction_from_live_register) + fraction_from_live_register * pay_fraction) * annual_average_industrial_wage)

# Yearly pay-out Projections for 15 years.
# (death rate is approximate from CSO 2014 for ages 55-65 ) http://www.cso.ie/en/releasesandpublications/ep/p-1916/1916irl/bmd/deaths/
death_rate = .1
population_55_65 =[(50,61988), (51, 61798), (52,60183),(53,58907),(54,57059),(55,57256),(56,54907),(57,54459),(58,52428),(59,51052),(60,49865),(61,49245),(62,47300),(63,47402),(64,45044),(65,44156)]
labour_participation_55_65 = .49

def attrition(pop):
    new_pop = {}
    for key in pop:
        new_pop[key] = pop[key] - pop[key] * death_rate
        
    return new_pop

def pay_average(year):
    years_in = 65 - year

def payouts_by_year():
    d = dict(population_55_65)
    oldest = 65

    cost_by_year = {}
    for i in range(0,15):
        total = 0
        for j in range(0,i):
            total += annual_average_industrial_wage * d[65-j]
                
        d = attrition(d)
        cost_by_year[i] = total * .60
            
    return cost_by_year.items()
            

if __name__ == "__main__":
    print "annual total: %d" % annual_total
    print "average cost of job seekers: %d" % annual_live_register_pay
    print "fraction of employment cost for job seekers: %.2f" % pay_fraction
    print "employable: %d" % employable
    print "expenditures by year: %s" % payouts_by_year()
    


"""
def jobsByYear(years):
    cumulative_capital = 0
    jby = []
    jobs = 0
    job_cost = 0
    for i in range(1,years):
        jobs += i * labour_capital_ratio
        capital_formation = (1 - labour_capital_ratio) * annual_total
        cumulative_capital += capital_formation
        jby.append({
            year : i,
            jobs : jobs,
            capital_formation : capital_formation,
            cumulative_capital : cumulative_capital
        })

"""

