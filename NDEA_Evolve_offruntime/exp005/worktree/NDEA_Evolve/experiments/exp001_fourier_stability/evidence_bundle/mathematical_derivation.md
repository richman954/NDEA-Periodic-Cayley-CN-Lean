
# Mathematical derivation

## Fourier symbol of the centered negative discrete Laplacian

Let a periodic phase mode be `phi_j = z^j`, with `z = exp(i theta)`. For a finite
periodic grid one normally takes `theta = 2*pi*m/N`, so `z^N = 1`. The centered
negative discrete Laplacian is

`(-Delta_h u)_j = (2*u_j - u_(j-1) - u_(j+1)) / h^2`.

On the mode, `phi_(j+1) = z*phi_j` and `phi_(j-1) = z^(-1)*phi_j`, hence its
Laurent symbol is

`(2 - z^(-1) - z) / h^2 = ((1-z)*(1-z^(-1))) / h^2`.

For a unit phase, `z + z^(-1) = 2*cos(theta)`. Therefore

`2 - z^(-1) - z = 2 - 2*cos(theta) = 4*sin(theta/2)^2`,

and the mode eigenvalue is

`lambda_h(theta) = (4/h^2)*sin(theta/2)^2`.

For real `theta` and nonzero real `h`, this is nonnegative. The physical headline
theorem uses the stronger and standard grid assumption `h > 0`.

## Cayley–Crank–Nicolson factor

For the scalar eigenmode update, write `a = (k/2)*lambda_h(theta)`. The modeled
Crank–Nicolson equation is

`(1 + i*a)*c_next = (1 - i*a)*c_current`.

The universally valid multiplier formulation is `c_next = G*c_current`, where

`G = (1 - i*a)/(1 + i*a)`.

Writing `G = c_next/c_current` additionally requires `c_current != 0`; the formal
development does not need that restriction. For real `a`,

`|1-i*a|^2 = 1+a^2 = |1+i*a|^2`.

The denominator cannot vanish because its squared modulus is at least one. Thus

`|G| = |1-i*a|/|1+i*a| = 1`.

## Sign control

Reversing the Laplacian sign changes `lambda` to `-lambda` but does not, by itself,
break a Cayley factor's unit modulus for real parameters. The sign error is
therefore detected at the stencil/eigenvalue/nonnegativity layer, where it is
mathematically relevant, rather than by pretending the modulus test distinguishes it.
