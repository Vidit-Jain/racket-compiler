(let ([y 2]) (- (let ([x (let ([x 11]) (+ (+ x (+ 1 (let ([y 12]) y))) y))]) (+ x 1)) y))
