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
#question = 1

train = pd.read_csv("bank_data/Bank_Data_Train.csv")
test = pd.read_csv("bank_data/Bank_Data_Test.csv")
fico_encoded = pd.get_dummies(pd.concat([train['FICO Range'],test['FICO Range']], axis=0),\
                              prefix='FICO Range', dummy_na=True)
loan_purpose_encoded = pd.get_dummies(pd.concat([train['Loan Purpose'],test['Loan Purpose']], axis=0),\
                                      prefix='Loan Purpose', dummy_na=True)
train_rows = train.shape[0]
fico_train_encoded = fico_encoded.iloc[:train_rows, :]
fico_test_encoded = fico_encoded.iloc[train_rows:, :]
loan_purpose_train_encoded = loan_purpose_encoded.iloc[:train_rows, :]
loan_purpose_test_encoded = loan_purpose_encoded.iloc[train_rows:, :]
train_conti_data = train[['Amount Requested','Interest Rate Percentage','Loan Length in Months','Debt-To-Income Ratio Percentage']].values
#normalize data
for j in range(4):
    ma = max(train_conti_data[:,j])
    mi = min(train_conti_data[:,j])
    m =  np.mean(train_conti_data[:,j])
    n =  np.std(train_conti_data[:,j])
    for index in range(train_rows):
        #train_conti_data[index,j] = (train_conti_data[index,j] - m)/n
        train_conti_data[index,j] = (train_conti_data[index,j] - mi)/(ma-mi)
#preprocessing.normalize(train_conti_data,axis=0,copy=False)
train_disc_data = np.column_stack((fico_train_encoded.values,loan_purpose_train_encoded.values))
train_target = train['Status'].values

for k_value in [5,10,100]:
    kf = KFold(train_rows, n_folds=k_value)
    clf_sum = 0
    lr_sum = 0
    svm_sum = 0
    for train, test in kf:
#NBC
        train_1 = train_disc_data[train]
        train_2 = train_conti_data[train]
        test_1 = train_disc_data[test]
        test_2 = train_conti_data[test]
        train_true = train_target[train]
        test_true = train_target[test]
        clf_train_disc = BernoulliNB()
        clf_train_disc.fit(train_1,train_true)
        clf_train_conti = GaussianNB()
        clf_train_conti.fit(train_2,train_true)
        result1 = clf_train_disc.predict_proba(test_1)
        result2 = clf_train_conti.predict_proba(test_2)
        result_arr = np.zeros(len(test), dtype=int)
        for index in range(len(test)):
            result_a = result1[index,0] * result2[index,0]
            result_b = result1[index,1] * result2[index,1]
            if (result_a < result_b): result_arr[index] = 1
            else: result_arr[index] = 0    
        clf_sum += f1_score(test_true,result_arr)
#logistic
        lr_data = np.column_stack((train_conti_data,train_disc_data))
        lr_train_data = lr_data[train]
        lr_test_data = lr_data[test]
        lr_train = LogisticRegression()
        lr_train.fit(lr_train_data, train_true)
        result_lr = lr_train.predict(lr_test_data)
        lr_sum += f1_score(test_true, result_lr)
#SVM
        svm_data = lr_data
        svm_train_data = svm_data[train]
        svm_test_data = svm_data[test]
        svm_train = svm.SVC(kernel='linear')
        svm_train.fit(svm_train_data, train_true)
        result_svm = svm_train.predict(svm_test_data)
        svm_sum += f1_score(test_true, result_svm)
    print "Avg. F1 score of NBC with K = {0}".format(k_value)
    print clf_sum/k_value
    print "Avg. F1 score of LogisticRegression with K = {0}".format(k_value)
    print lr_sum/k_value
    print "Avg. F1 score of SVM with K = {0}".format(k_value)
    print svm_sum/k_value


