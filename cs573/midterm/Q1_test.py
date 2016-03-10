import numpy as np
import pandas as pd
from sklearn.naive_bayes import BernoulliNB
from sklearn.naive_bayes import GaussianNB
from sklearn.naive_bayes import MultinomialNB
from sklearn.metrics import classification_report
from sklearn.metrics import f1_score
from sklearn.cross_validation import KFold
from sklearn import preprocessing
from sklearn.linear_model import LogisticRegression
from sklearn import svm

train = pd.read_csv("bank_data/Bank_Data_Train.csv")
test = pd.read_csv("bank_data/Bank_Data_Test.csv")

fico_encoded = pd.get_dummies(pd.concat([train['FICO Range'],test['FICO Range']], axis=0),\
                              prefix='FICO Range', dummy_na=True)
loan_purpose_encoded = pd.get_dummies(pd.concat([train['Loan Purpose'],test['Loan Purpose']], axis=0),\
                                      prefix='Loan Purpose', dummy_na=True)
train_rows = train.shape[0]
test_rows = test.shape[0]
fico_train_encoded = fico_encoded.iloc[:train_rows, :]
fico_test_encoded = fico_encoded.iloc[train_rows:, :]
loan_purpose_train_encoded = loan_purpose_encoded.iloc[:train_rows, :]
loan_purpose_test_encoded = loan_purpose_encoded.iloc[train_rows:, :]
train_conti_data = train[['Amount Requested','Interest Rate Percentage','Loan Length in Months','Debt-To-Income Ratio Percentage']].values
test_conti_data = test[['Amount Requested','Interest Rate Percentage','Loan Length in Months','Debt-To-Income Ratio Percentage']].values

#normalize data
for j in range(4):
    ma = max(test_conti_data[:,j])
    mi = min(test_conti_data[:,j])
    m =  np.mean(test_conti_data[:,j])
    n =  np.std(test_conti_data[:,j])
    for index in range(test_rows):
        test_conti_data[index,j] = (test_conti_data[index,j] - mi)/(ma-mi)

for j in range(4):
    ma = max(train_conti_data[:,j])
    mi = min(train_conti_data[:,j])
    m =  np.mean(train_conti_data[:,j])
    n =  np.std(train_conti_data[:,j])
    for index in range(train_rows):
        train_conti_data[index,j] = (train_conti_data[index,j] - mi)/(ma-mi)

train_disc_data = np.column_stack((fico_train_encoded.values,loan_purpose_train_encoded.values))
test_disc_data = np.column_stack((fico_test_encoded.values,loan_purpose_test_encoded.values))
train_target = train['Status'].values

#NBC
clf_train_disc = BernoulliNB()
clf_train_disc.fit(train_disc_data,train_target)
clf_train_conti = GaussianNB()
clf_train_conti.fit(train_conti_data,train_target)
result1 = clf_train_disc.predict_proba(test_disc_data)
result2 = clf_train_conti.predict_proba(test_conti_data)
result_arr = np.zeros(test_rows, dtype=int)
for index in range(test_rows):
    result_a = result1[index,0] * result2[index,0]
    result_b = result1[index,1] * result2[index,1]
    if (result_a < result_b): result_arr[index] = 1
    else: result_arr[index] = 0
print result_arr
record_num = test['Record Number'].values
output = pd.DataFrame(np.column_stack((record_num,result_arr)),\
                      columns=['Record Number', 'Status'])
#output.to_csv("naive_result.csv")

svm_train_data = np.column_stack((train_conti_data,train_disc_data))
svm_test_data = np.column_stack((test_conti_data,test_disc_data))
svm_train = svm.SVC()
svm_train.fit(svm_train_data, train_target)
result_svm = svm_train.predict(svm_test_data)
print result_svm
record_num = test['Record Number'].values
output = pd.DataFrame(np.column_stack((record_num,result_svm)),\
                      columns=['Record Number', 'Status'])
print output
#output.to_csv("SVM_result.csv")

lr_train_data = np.column_stack((train_conti_data[1000:2500],train_disc_data[1000:2500]))
lr_test_data = np.column_stack((test_conti_data,test_disc_data))
lr_train = LogisticRegression()
lr_train.fit(lr_train_data, train_target[1000:2500])
result_lr = lr_train.predict(lr_test_data)
print result_lr
record_num = test['Record Number'].values
output = pd.DataFrame(np.column_stack((record_num,result_lr)),\
                      columns=['Record Number', 'Status'])
print output
output.to_csv("LR_result.csv")

