# Q3.i & 2
if(FALSE){
ucb_test <- function(k, ntest, dataSet){
    #K := 4 in this question
    k = 4
    pull_times = matrix(nrow = k, ncol = ntest)
    for(i in 1:k){
    	  for(j in 1:ntest){
	      pull_times[i,j] = 0
        }
    }
    ni = 1:k
    ri = 1:k
    # initialize ni and rewards to 0
    for (i in 1:4) {
        ni[i] = 0
    	ri[i] = 0
    }

    if (dataSet == 'b') {
        v1b = read.csv("other_donation_data/population1b.csv", header=TRUE)
    	v2b = read.csv("other_donation_data/population2b.csv", header=TRUE)
	v3b = read.csv("other_donation_data/population3b.csv", header=TRUE)
	v4b = read.csv("other_donation_data/population4b.csv", header=TRUE)
	v1b_m = as.matrix(v1b)
        v2b_m = as.matrix(v2b)
        v3b_m = as.matrix(v3b)
        v4b_m = as.matrix(v4b)
    }

    else if (dataSet == 'p') {
        v1b = read.csv("other_donation_data/population1p.csv", header=TRUE)
    	v2b = read.csv("other_donation_data/population2p.csv", header=TRUE)
	v3b = read.csv("other_donation_data/population3p.csv", header=TRUE)
	v4b = read.csv("other_donation_data/population4p.csv", header=TRUE)
	#normalize all data
	v1b_m = as.matrix(v1b)
        v2b_m = as.matrix(v2b)
        v3b_m = as.matrix(v3b)
        v4b_m = as.matrix(v4b)
	#find the largest number
	max_value = max(c(max(v1b_m[1:ntest,2]),max(v2b_m[1:ntest,2]),max(v3b_m[1:ntest,2]),max(v4b_m[1:ntest,2])))
        v1b_m[,2] = unlist(lapply(v1b_m[,2], function(x){return(x/max_value)}))
        v2b_m[,2] = unlist(lapply(v2b_m[,2], function(x){return(x/max_value)}))
        v3b_m[,2] = unlist(lapply(v3b_m[,2], function(x){return(x/max_value)}))
	v4b_m[,2] = unlist(lapply(v4b_m[,2], function(x){return(x/max_value)}))
    }
    arm_reward_dist = list(v1b_m, v2b_m, v3b_m, v4b_m)

    selectNextArm <- function() {
        scores <- 1:4
	maxIndex = 0
	maxScore = 0
	for(m in 1:4){
	    if (ni[m] == 0) {return(m)}
	    scores[m] = (ri[m] / ni[m]) + sqrt(2.0 * log(i) / ni[m])
	    if (maxIndex == 0) {maxIndex = 1; maxScore = scores[1]}
	    else if (maxScore < scores[m]) {maxIndex = m; maxScore = scores[m]}
        }
	return(maxIndex)
    }

    updateStatus <- function(i_arm) {
        ni[i_arm] <<- ni[i_arm] + 1
        for(j in 1:k){
	    pull_times[j, i] <<- ni[j]
        }
	ri[i_arm] <<- ri[i_arm] + arm_reward_dist[[i_arm]][ni[i_arm], 2]
    }

    #output the result for (a) and plot for (b)
    outputResult <- function() {
        line = 0
	rewards = c(0,0,0,0)
	for(i in 1:4) {
            # 	  print(ni[i])
	    line = line + ni[i]
	    #	  print(ri[i])
	    if (dataSet == 'p') {rewards[i] = rewards[i] + ri[i] * max_value}
	    else {rewards[i] = rewards[i] + ri[i]}
        }
	print(sum(rewards))
	return(pull_times)
    }

########################

    arm = 0
    for (i in 1:ntest) {
        arm = selectNextArm()
	updateStatus(arm)
    }
    return(outputResult())
}

########################

x=c()
y=c()

flag = 'b'

x <- 1:1000
y <- ucb_test(4, 1000, flag)
plot(x, y[1,], xlim=c(0, 1400), ylim=c(0, 400), type="l", main="ucb_test: total pulls vs. pulls of each arm", xlab="number of pulls", ylab="pulled times", col="blue", lwd=1.5)
lines(x, y[2,], type="l", col="red", lwd=1.5)
lines(x, y[3,], type="l", col="orange", lwd=1.5)
lines(x, y[4,], type="l", col="purple", lwd=1.5)

legend('topright', c("arm 1","arm 2","arm 3","arm 4"), bty='n', lty=1, lwd=1.5, col=c("blue","red", "orange", "purple"))

#Q3.i & ii

#end Q3.i

}

################################################################################
# Q3.3
if(FALSE){
e_greedy_test <- function(k, ntest, dataSet){
    #K := 4 in this question
    k = 4
    pull_times = matrix(nrow = k, ncol = ntest)
    for(i in 1:k){
    	  for(j in 1:ntest){
	      pull_times[i,j] = 0
        }
    }
    ni = 1:k
    ri = 1:k
    # initialize ni and rewards to 0
    for (i in 1:4) {
        ni[i] = 0
    	ri[i] = 0
    }

    if (dataSet == 'b') {
        v1b = read.csv("other_donation_data/population1b.csv", header=TRUE)
    	v2b = read.csv("other_donation_data/population2b.csv", header=TRUE)
	v3b = read.csv("other_donation_data/population3b.csv", header=TRUE)
	v4b = read.csv("other_donation_data/population4b.csv", header=TRUE)
	v1b_m = as.matrix(v1b)
        v2b_m = as.matrix(v2b)
        v3b_m = as.matrix(v3b)
        v4b_m = as.matrix(v4b)
    }

    else if (dataSet == 'p') {
        v1b = read.csv("other_donation_data/population1p.csv", header=TRUE)
    	v2b = read.csv("other_donation_data/population2p.csv", header=TRUE)
	v3b = read.csv("other_donation_data/population3p.csv", header=TRUE)
	v4b = read.csv("other_donation_data/population4p.csv", header=TRUE)
	#normalize all data
	v1b_m = as.matrix(v1b)
        v2b_m = as.matrix(v2b)
        v3b_m = as.matrix(v3b)
        v4b_m = as.matrix(v4b)
	#find the largest number
	max_value = max(c(max(v1b_m[1:ntest,2]),max(v2b_m[1:ntest,2]),max(v3b_m[1:ntest,2]),max(v4b_m[1:ntest,2])))
        v1b_m[,2] = unlist(lapply(v1b_m[,2], function(x){return(x/max_value)}))
        v2b_m[,2] = unlist(lapply(v2b_m[,2], function(x){return(x/max_value)}))
        v3b_m[,2] = unlist(lapply(v3b_m[,2], function(x){return(x/max_value)}))
	v4b_m[,2] = unlist(lapply(v4b_m[,2], function(x){return(x/max_value)}))
    }
    arm_reward_dist = list(v1b_m, v2b_m, v3b_m, v4b_m)
    
    selectNextArm <- function() {
        scores <- 1:4
	gaps <- 1:4
	maxIndex = 0
	maxScore = 0
	for(m in 1:4){
	    if (ni[m] == 0) {return(m)}
	    scores[m] = (ri[m] / ni[m])
	    if (maxIndex == 0) {maxIndex = 1; maxScore = scores[1]}
	    else if (maxScore < scores[m]) {maxIndex = m; maxScore = scores[m]}
        }
	#calculate gaps
	minGap = 1
	for(m in 1:4){
            gaps[m] = maxScore - scores[m]
	    if (gaps[m] == 0) {next}
	    else if(gaps[m] < minGap) {minGap = gaps[m]}
        }
	#calculate epsilon
	epsilon = min(c(12/sqrt(minGap ** 2 * i),1))
	#Random
	rand_num = runif(1, 0, 1)
	if(rand_num < epsilon) {maxIndex = floor(runif(1, 0, 4)) + 1; if(maxIndex == 5) {maxIndex = 4}}
	return(maxIndex)
    }

    updateStatus <- function(i_arm) {
        ni[i_arm] <<- ni[i_arm] + 1
	for(j in 1:k){
	    pull_times[j, i] <<- ni[j]
        }
	ri[i_arm] <<- ri[i_arm] + arm_reward_dist[[i_arm]][ni[i_arm], 2]
    }

    #output the result for (a) and plot for (b)
    outputResult <- function() {
        line = 0
	rewards = c(0,0,0,0)
	for(i in 1:4) {
            # 	  print(ni[i])
	    line = line + ni[i]
	    #	  print(ri[i])
	    if (dataSet == 'p') {rewards[i] = rewards[i] + ri[i] * max_value}
	    else {rewards[i] = rewards[i] + ri[i]}
        }
	print(sum(rewards))
	return(pull_times)
    }

########################

    arm = 0
    for (i in 1:ntest) {
        arm = selectNextArm()
	updateStatus(arm)
    }
    return(outputResult())
}

########################
#Q3.iii
x=c()
y=c()

flag = 'b'

x <- 1:1000
y <- e_greedy_test(4, 1000, flag)
plot(x, y[1,], xlim=c(0, 1400), ylim=c(0, 300), type="l", main="e_greedy_test: pulls vs. pulls of each arm", xlab="number of pulls", ylab="pulled times", col="blue", lwd=1.5)
lines(x, y[2,], type="l", col="red", lwd=1.5)
lines(x, y[3,], type="l", col="orange", lwd=1.5)
lines(x, y[4,], type="l", col="purple", lwd=1.5)

legend('topright', c("arm 1","arm 2","arm 3","arm 4"), bty='n', lty=1, lwd=1.5, col=c("blue","red", "orange", "purple"))
}

#Q3.v
if(FALSE){
ts_test <- function(k, ntest, dataSet, alpha, beta){
    #K := 4 in this question
    k = 4
    pull_times = matrix(nrow = k, ncol = ntest)
    for(i in 1:k){
    	  for(j in 1:ntest){
	      pull_times[i,j] = 0
        }
    }
    S = 1:k
    F = 1:k
    # initialize ni and rewards to 0
    for (i in 1:4) {
        S[i] = 0
    	F[i] = 0
    }

    ni = 1:k
    ri = 1:k
    # initialize ni and rewards to 0
    for (i in 1:4) {
        ni[i] = 0
    	ri[i] = 0
    }

    if (dataSet == 'b') {
        v1b = read.csv("other_donation_data/population1b.csv", header=TRUE)
    	v2b = read.csv("other_donation_data/population2b.csv", header=TRUE)
	v3b = read.csv("other_donation_data/population3b.csv", header=TRUE)
	v4b = read.csv("other_donation_data/population4b.csv", header=TRUE)
	v1b_m = as.matrix(v1b)
        v2b_m = as.matrix(v2b)
        v3b_m = as.matrix(v3b)
        v4b_m = as.matrix(v4b)
    }

    else if (dataSet == 'p') {
        v1b = read.csv("other_donation_data/population1p.csv", header=TRUE)
    	v2b = read.csv("other_donation_data/population2p.csv", header=TRUE)
	v3b = read.csv("other_donation_data/population3p.csv", header=TRUE)
	v4b = read.csv("other_donation_data/population4p.csv", header=TRUE)
	#normalize all data
	v1b_m = as.matrix(v1b)
        v2b_m = as.matrix(v2b)
        v3b_m = as.matrix(v3b)
        v4b_m = as.matrix(v4b)
	#find the largest number
	max_value = max(c(max(v1b_m[1:ntest,2]),max(v2b_m[1:ntest,2]),max(v3b_m[1:ntest,2]),max(v4b_m[1:ntest,2])))
        v1b_m[,2] = unlist(lapply(v1b_m[,2], function(x){return(x/max_value)}))
        v2b_m[,2] = unlist(lapply(v2b_m[,2], function(x){return(x/max_value)}))
        v3b_m[,2] = unlist(lapply(v3b_m[,2], function(x){return(x/max_value)}))
	v4b_m[,2] = unlist(lapply(v4b_m[,2], function(x){return(x/max_value)}))
    }
    arm_reward_dist = list(v1b_m, v2b_m, v3b_m, v4b_m)

    selectNextArm <- function() {
        #draw a random sample from beta
	scores <- 1:k
	maxIndex = 0
	maxScore = 0
	for (m in 1:k) {
            scores[m] = rbeta(1,S[m] + alpha, F[m] + beta)
#	    scores[m] = (S[m] + alpha)/(S[m] + F[m] + alpha + beta)
	    if (maxIndex == 0) {maxIndex = 1; maxScore = scores[1]}
	    else if (maxScore < scores[m]) {maxIndex = m; maxScore = scores[m]}
	}
	return(maxIndex)

    }

    updateStatus <- function(i_arm) {
        ni[i_arm] <<- ni[i_arm] + 1
	for(j in 1:k){
	    pull_times[j, i] <<- ni[j]
        }
	ri[i_arm] <<- ri[i_arm] + arm_reward_dist[[i_arm]][ni[i_arm], 2]
	tmp = arm_reward_dist[[i_arm]][ni[i_arm], 2]
	S[i_arm] <<- S[i_arm] + tmp
	F[i_arm] <<- F[i_arm] - tmp + 1
    }

    #output the result for (a) and plot for (b)
    outputResult <- function() {
        line = 0
	rewards = c(0,0,0,0)
	for(i in 1:4) {
            # 	  print(ni[i])
	    line = line + ni[i]
	    #	  print(ri[i])
	    if (dataSet == 'p') {rewards[i] = rewards[i] + ri[i] * max_value}
	    else {rewards[i] = rewards[i] + ri[i]}
        }
	print(sum(rewards))
	return(pull_times)
    }

########################

    arm = 0
    for (i in 1:ntest) {
        arm = selectNextArm()
	updateStatus(arm)
    }
    return(outputResult())
}

########################

x=c()
y=c()

flag = 'b'

x <- 1:1000
y <- ts_test(4, 1000, flag, 100, 100)
plot(x, y[1,], xlim=c(0, 1400), ylim=c(0, 1000), type="l", main="ts_test: pulls vs. rewards", xlab="number of pulls", ylab="pulled times", col="blue", lwd=1.5)
lines(x, y[2,], type="l", col="red", lwd=1.5)
lines(x, y[3,], type="l", col="orange", lwd=1.5)
lines(x, y[4,], type="l", col="purple", lwd=1.5)

legend('topright', c("arm 1","arm 2","arm 3","arm 4"), bty='n', lty=1, lwd=1.5, col=c("blue","red", "orange", "purple"))
}