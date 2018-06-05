#!/usr/bin/env pytho

user = {'username' : "Ralph",
        'age' : 12,
        'smoker' : True,
        'address' : "12 Elm St"}

quote = {'quote_id' : 3,
         'total' : 3000,
         'denomination' : 'euro',
         'period' : 'yearly'}

credit_card = {'credit_card_number' : 12}
         
def calculates_quote(user):
    return quote

def merchant_account_processing(quote,credit_card):
    if quote['total'] > 3:
        return {'policy_id' : 12,
                'expiry' : "24/03/2087"}
    else :
        return "Failure to process account"
    
def server(request, objs):
    if request == 'user_channel' :
        user = objs[0]
        quote = calculates_quote(user)
        return quote
    elif request == 'purchase_channel':
        quote = objs[0]
        credit_card = objs[1]
        certificate = merchant_account_processing(quote,credit_card)
        print certificate
        return certificate
    else :
        return "No such channel"


if __name__ == "__main__":
    quote = server('user_channel', [user])
    cert = server('purchase_channel', [quote,credit_card])
    
