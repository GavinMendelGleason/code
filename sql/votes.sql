-- sudo -i -u postgres
-- psql votes

CREATE TABLE votes
(
  id serial NOT NULL,	
  motion_name text,
  motion_description text,
  motion_subject text,
  councillor varchar(50),
  party varchar(50),
  vote varchar(15),
  CONSTRAINT votes_pkey PRIMARY KEY (id)	
);

COPY votes(motion_name,motion_description,motion_subject,councillor,party,vote)
FROM '/home/francoisbabeuf/Documents/workersparty/Votes.csv' DELIMITER ',' CSV HEADER;

CREATE TABLE co_votes AS
select v1.motion_name as motion_name,
v1.councillor as councillor_a,
v1.party as party_a,
v2.councillor as councillor_b,
v2.party as party_b, v1.vote
from votes as v1, votes as v2
where v1.motion_name=v2.motion_name
--and v1.councillor <> v2.councillor
and v1.vote = v2.vote;

COPY (select councillor_a, party_a, councillor_b, party_b, count(*) from co_votes
group by councillor_a, party_a, councillor_b, party_b
order by count(*) desc) TO '/tmp/councillor.csv' DELIMITER ',' CSV HEADER;


COPY (select party_a, party_b, count(*) from co_votes
group by party_a, party_b
order by count(*) desc) TO '/tmp/party.csv' DELIMITER ',' CSV HEADER;

CREATE TABLE party_co_votes AS
select v1.motion_name as motion_name,
v1.councillor as councillor_a,
v1.party as party_a,
v2.councillor as councillor_b,
v2.party as party_b, v1.vote
from votes as v1, votes as v2
where v1.motion_name=v2.motion_name
and v1.vote = v2.vote;

-- Councillor totals
CREATE TABLE councillor_totals AS
select councillor_a, count(*) from co_votes
where councillor_a = councillor_b
group by councillor_a
order by count(*) desc;

-- Party totals
CREATE TABLE party_totals AS
select party_a, count(*) from co_votes
where party_a = party_b
group by party_a
order by count(*) desc;

CREATE TABLE co_vote_totals AS
(select councillor_a, councillor_b, party_a, party_b, sum(count) from
 (select councillor_a, councillor_b, party_a, party_b, count(vote) from co_votes
  group by councillor_a, councillor_b, party_a, party_b, vote) as totals
 group by councillor_a, councillor_b, party_a, party_b);

CREATE TABLE similarity_matrix AS
select Votes.councillor_a, Votes.councillor_b, Votes.party_a, Votes.party_b,
((2.0 * Votes.sum) / (total_a + total_b)) as distance from
(select * from co_vote_totals) as Votes, 
(select councillor_a, count as total_a from councillor_totals) as A_total,
(select councillor_a, count as total_b from councillor_totals) as B_total
where Votes.councillor_a = A_total.councillor_a
and Votes.councillor_b = B_total.councillor_a
order by distance desc;

COPY (select * from similarity_matrix) TO '/tmp/similarity.csv' DELIMITER ',' CSV HEADER;

CREATE TABLE co_vote_party_totals AS
(select party_a, party_b, sum(count) from
 (select party_a, party_b, count(vote) from co_votes
  group by party_a, party_b, vote) as totals
 group by party_a, party_b);


CREATE TABLE party_similarity_matrix AS
select Votes.party_a, Votes.party_b,
((2.0 * Votes.sum) / (total_a + total_b)) as distance from
(select * from co_vote_party_totals) as Votes, 
(select party_a, count as total_a from party_totals) as A_total,
(select party_a, count as total_b from party_totals) as B_total
where Votes.party_a = A_total.party_a
and Votes.party_b = B_total.party_a
order by distance desc;

COPY (select * from party_similarity_matrix) TO '/tmp/party_similarity.csv' DELIMITER ',' CSV HEADER;

CREATE TABLE housing_co_votes AS
select v1.motion_name as motion_name,
v1.councillor as councillor_a,
v1.party as party_a,
v2.councillor as councillor_b,
v2.party as party_b, v1.vote
from votes as v1, votes as v2
where v1.motion_name=v2.motion_name
and v1.motion_subject like '%housing and homelessness%'
and v1.vote = v2.vote;

COPY (select councillor_a, party_a, councillor_b, party_b, count(*) from housing_co_votes
group by councillor_a, party_a, councillor_b, party_b
order by count(*) desc) TO '/tmp/housing_councillor.csv' DELIMITER ',' CSV HEADER;

CREATE TABLE housing_councillor_totals AS
select councillor_a, count(*) from housing_co_votes
where councillor_a = councillor_b
group by councillor_a
order by count(*) desc;

CREATE TABLE housing_co_vote_totals AS
(select councillor_a, councillor_b, party_a, party_b, sum(count) from
 (select councillor_a, councillor_b, party_a, party_b, count(vote) from housing_co_votes
  group by councillor_a, councillor_b, party_a, party_b, vote) as totals
 group by councillor_a, councillor_b, party_a, party_b);

CREATE TABLE housing_similarity_matrix AS
select Votes.councillor_a, Votes.councillor_b, Votes.party_a, Votes.party_b,
((2.0 * Votes.sum) / (total_a + total_b)) as distance from
(select * from housing_co_vote_totals) as Votes, 
(select councillor_a, count as total_a from councillor_totals) as A_total,
(select councillor_a, count as total_b from councillor_totals) as B_total
where Votes.councillor_a = A_total.councillor_a
and Votes.councillor_b = B_total.councillor_a
order by distance desc;

