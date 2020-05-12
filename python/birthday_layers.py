from bigfloat import *
import math

def p(l,k):
    Numerator = BigFloat.exact(l ** 2)
    Denominator = BigFloat.exact(2 * k)
    E = BigFloat.exact(2.71828182845904523536028747135266249775724709369995)

    return 1 - (E ** (- (Numerator / (1.0 * Denominator))))


def example():
    Days = 365
    years = 1000
    transactions_per_day = 1000
    users = 1000000000
    layer_size = BigFloat.exact(2 ** 160)
    layers = Days * years * transactions_per_day * users
    return p(layers , layer_size)
