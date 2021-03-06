dem = read.csv("dem.csv",header=TRUE,colClasses=c(candidate_id="integer",donation="numeric",state="character"))
gop = read.csv("gop.csv",header=TRUE,colClasses=c(candidate_id="integer",donation="numeric",state="character"))

demdonations = as.matrix(dem$donation[dem$donation > 0])
gopdonations = as.matrix(gop$donation[gop$donation > 0])

N = round(nrow(demdonations)/200)

# randomly split DEMs into N groups of average length nrow(demdonations)/N
demsplit = as.list(split(demdonations, sample(1:N, nrow(demdonations), replace=T)))

# find average of each bin
dem_bin_averages = unlist(lapply(demsplit,mean))

# find 20 quantiles of each the batch averages
# quantiles_dem = quantile(dem_bin_averages,probs = seq(0, 1, 1/20))

# plot histogram
# hist(dem_bin_averages,main="Histogram of DEM Batches (Average Donations)",freq=FALSE,breaks=quantiles_dem,xlim=c(0,4000))


N = round(nrow(gopdonations)/200)

# randomly split GOP into N groups of average length nrow(demdonations)/N
gopsplit = split(gopdonations, sample(1:N, nrow(gopdonations), replace=T))

# find average of each bin
gop_bin_averages = unlist(lapply(gopsplit,mean))

# find 20 quantiles of each the batch averages
# quantiles_gop = quantile(gop_bin_averages,probs = seq(0, 1, 1/20))

# plot histogram
# hist(gop_bin_averages,main="Histogram of GOP Batches (Average Donations)",freq=FALSE,breaks=quantiles_gop,xlim=c(0,4000))

# Q1.ii
# t.test(dem_bin_averages, gop_bin_averages, alternative="less")
# p<-t.test(dem_bin_averages, gop_bin_averages, alternative="less")$p.value
# print(p)

# Q1.vi
# (ii)
gop_tmp = gop[gop$donation > 0,]
dem_tmp = dem[dem$donation > 0,]

gop_cand_matrix = as.matrix(aggregate(gop_tmp$donation, by=list(candidate_id=gop_tmp$candidate_id), FUN=sum))
colnames(gop_cand_matrix) <- c("candidate_id", "donation")
dem_cand_matrix = as.matrix(aggregate(dem_tmp$donation, by=list(candidate_id=dem_tmp$candidate_id), FUN=sum))
colnames(dem_cand_matrix) <- c("candidate_id", "donation")

if(FALSE){
print(gop_cand_matrix)
print(dem_cand_matrix)
}

N = round(nrow(gop_cand_matrix)/30)
gop_cand_split = as.list(split(gop_cand_matrix, sample(1:N, nrow(gop_cand_matrix), replace=T)))
# find average of each bin
gop_cand_bin_averages = unlist(lapply(gop_cand_split,mean))

N = round(nrow(dem_cand_matrix)/30)
dem_cand_split = as.list(split(dem_cand_matrix, sample(1:N, nrow(dem_cand_matrix), replace=T)))
# find average of each bin
dem_cand_bin_averages = unlist(lapply(dem_cand_split,mean))
t.test(dem_bin_averages, gop_bin_averages, alternative="less")
p<-t.test(dem_cand_bin_averages, gop_cand_bin_averages, alternative="less")$p.value
print(p)


# Q1.iii & Q1.v
# dem states: AK AL AR AZ CA CO CT DE FL GA HI IA ID IL IN KS KY LA MA MD ME MI MN MO MS MT NC ND NE NH NJ NM NV NY OH OK OR PA RI SC SD TN TX UT VA VT WA WI WV
dem_data = dem[!dem$state %in% c("VT", "WY"),]
dem_matrix = as.matrix(dem_data)
# print(t[1:10, "donation"])
# print(t[1:100,c(1,2,3)])

gop_data = gop[!gop$state %in% c("VT", "WY"),]
gop_matrix = as.matrix(gop_data)

count1 = 0
count2 = 0
states <- c("AK", "AL", "AR", "AZ", "CA", "CO", "CT", "DE", "FL", "GA", "HI", "IA", "ID", "IL", "IN", "KS", "KY", "LA", "MA", "MD", "ME", "MI", "MN", "MO", "MS", "MT", "NC", "ND", "NE", "NH", "NJ", "NM", "NV", "NY", "OH", "OK", "OR", "PA", "RI", "SC", "SD", "TN", "TX", "UT", "VA", "WA", "WI", "WV")
for (state in states) {
    gop_tmp = gop[gop$state %in% state & (gop$donation > 0),]
    gop_tmp_matrix = as.matrix(gop_tmp$donation)
    dem_tmp = dem[dem$state %in% state & (dem$donation > 0),]
    dem_tmp_matrix = as.matrix(dem_tmp$donation)
    print(state)

if(FALSE){    
    N = round(nrow(gop_tmp_matrix)/30)
    if (N < 3) {
       print(paste("not enough observations for state:", state, sep=" "))
       next
    }

    # randomly split DEMs into N groups of average length nrow(demdonations)/N
    gop_state_split = as.list(split(gop_tmp_matrix, sample(1:N, nrow(gop_tmp_matrix), replace=T)))
    
    # find average of each bin
    gop_state_bin_averages = unlist(lapply(gop_state_split,mean))

    N = round(nrow(dem_tmp_matrix)/30)
    if (N < 3) {
       print(paste("not enough observations for state:", state, sep=" "))
       next
    }

    dem_state_split = as.list(split(dem_tmp_matrix, sample(1:N, nrow(dem_tmp_matrix), replace=T)))
    
    # find average of each bin
    dem_state_bin_averages = unlist(lapply(dem_state_split,mean))

    # Q1.iii
    p<-t.test(dem_state_bin_averages, gop_state_bin_averages, alternative="less")$p.value
    print(p)
    if (p < 0.05) count1 = count1 + 1

    # Q1.v
    p<-t.test(dem_state_bin_averages, gop_state_bin_averages, alternative="greater")$p.value
    print(p)
    if (p < 0.05) count2 = count2 + 1
}

    # Q1.vi
    # (iii)
    # foreach state, sum up the data grouping by candidate
    # call t.test (bin or not bin?)
    gop_tmp_cand_matrix = as.matrix(aggregate(gop_tmp$donation, by=list(candidate_id=gop_tmp$candidate_id), FUN=sum))
    colnames(gop_tmp_cand_matrix) <- c("candidate_id", "donation")
    dem_tmp_cand_matrix = as.matrix(aggregate(dem_tmp$donation, by=list(candidate_id=dem_tmp$candidate_id), FUN=sum))
    colnames(dem_tmp_cand_matrix) <- c("candidate_id", "donation")
    
    # Shall we calculate bin_avg??
    p<-t.test(dem_tmp_cand_matrix, gop_tmp_cand_matrix, alternative="less")$p.value
    print(p)

}
# Q1.iv
# print(count1); print(count2)
