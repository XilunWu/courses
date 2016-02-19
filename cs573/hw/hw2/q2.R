# 1
if(FALSE) {
v1b = read.csv("other_donation_data/population1b.csv", header=TRUE)
v2b = read.csv("other_donation_data/population2b.csv", header=TRUE)

v1b_m = as.matrix(v1b$donates)
v2b_m = as.matrix(v2b$donates)

N = round(nrow(v1b_m)/200)
v1b_split = as.list(split(v1b_m, sample(1:N, nrow(v1b_m), replace=T)))
N = round(nrow(v2b_m)/200)
v2b_split = as.list(split(v2b_m, sample(1:N, nrow(v2b_m), replace=T)))

v1b_bin_averages = unlist(lapply(v1b_split,mean))
v2b_bin_averages = unlist(lapply(v2b_split,mean))

# t.test(v1b_bin_averages, v2b_bin_averages, alternative="less")
# p<-t.test(dem_bin_averages, v2b_bin_averages, alternative="less")$p.value
# print(p)

v1b_mean = mean(v1b_m)
v2b_mean = mean(v2b_m)

print(v1b_mean)
print(v2b_mean)
}

# 2
if(FALSE) {
v1b = read.csv("other_donation_data/population3b.csv", header=TRUE)
v2b = read.csv("other_donation_data/population4b.csv", header=TRUE)

v1b_m = as.matrix(v1b$donates)
v2b_m = as.matrix(v2b$donates)

N = round(nrow(v1b_m)/50)
v1b_split = as.list(split(v1b_m, sample(1:N, nrow(v1b_m), replace=T)))
N = round(nrow(v2b_m)/50)
v2b_split = as.list(split(v2b_m, sample(1:N, nrow(v2b_m), replace=T)))

v1b_bin_averages = unlist(lapply(v1b_split,mean))
v2b_bin_averages = unlist(lapply(v2b_split,mean))

# t.test(v1b_bin_averages, v2b_bin_averages, alternative="less")
# p<-t.test(dem_bin_averages, v2b_bin_averages, alternative="less")$p.value
# print(p)

v1b_mean = mean(v1b_m)
v2b_mean = mean(v2b_m)

print(v1b_mean)
print(v2b_mean)
}

# 3
if(FALSE) {
v1b = read.csv("other_donation_data/population1p.csv", header=TRUE)
v2b = read.csv("other_donation_data/population2p.csv", header=TRUE)

v1b_m = as.matrix(v1b$donates)
v2b_m = as.matrix(v2b$donates)

N = round(nrow(v1b_m)/200)
v1b_split = as.list(split(v1b_m, sample(1:N, nrow(v1b_m), replace=T)))
N = round(nrow(v2b_m)/200)
v2b_split = as.list(split(v2b_m, sample(1:N, nrow(v2b_m), replace=T)))

v1b_bin_averages = unlist(lapply(v1b_split,mean))
v2b_bin_averages = unlist(lapply(v2b_split,mean))

# t.test(v1b_bin_averages, v2b_bin_averages, alternative="less")
# p<-t.test(dem_bin_averages, v2b_bin_averages, alternative="less")$p.value
# print(p)

v1b_mean = mean(v1b_m)
v2b_mean = mean(v2b_m)

print(v1b_mean)
print(v2b_mean)
}


# 4
#if(FALSE) {
v1b = read.csv("other_donation_data/population3p.csv", header=TRUE)
v2b = read.csv("other_donation_data/population4p.csv", header=TRUE)

v1b_m = as.matrix(v1b$donates)
v2b_m = as.matrix(v2b$B)

N = round(nrow(v1b_m)/50)
v1b_split = as.list(split(v1b_m, sample(1:N, nrow(v1b_m), replace=T)))
N = round(nrow(v2b_m)/50)
v2b_split = as.list(split(v2b_m, sample(1:N, nrow(v2b_m), replace=T)))

v1b_bin_averages = unlist(lapply(v1b_split,mean))
v2b_bin_averages = unlist(lapply(v2b_split,mean))

# t.test(v1b_bin_averages, v2b_bin_averages, alternative="less")
# p<-t.test(dem_bin_averages, v2b_bin_averages, alternative="less")$p.value
# print(p)

v1b_mean = mean(v1b_m)
v2b_mean = mean(v2b_m)

print(v1b_mean)
print(v2b_mean)
#}