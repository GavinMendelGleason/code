from lecture9 import *
server = Server()
catalogue = Catalogue()
customer = Customer(catalogue,server)
customer.register("me","pass")
customer.login("me","pass")
customer.browse()
customer.select('t-shirt')
