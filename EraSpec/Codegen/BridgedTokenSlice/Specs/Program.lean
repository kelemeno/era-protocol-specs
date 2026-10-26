import EraSpec.Codegen.Lang

/-!
# The bridged-token mint/burn slice as a `Codegen` program

Transcribed from era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`bridge/BridgedStandardERC20.sol` (`onlyNTV`, `bridgeMint`, `bridgeBurn`) and the
OpenZeppelin v4 `ERC20Upgradeable` it inherits at submodule commit
`2d081f24cac1a867f6f73d512f2022e1fa987854` (`transfer`, `_transfer`, `_mint`,
`_burn`, `balanceOf`, `totalSupply`).  Each body keeps the source's check order,
revert data and `unchecked` placement, so the two implementations can be compared
on revert bytes and logs, not only on success.

Deliberate differences, all outside the comparison scope (`CODE_GENERATION.md`):

* The vault is a constructor argument and must be nonzero.  The original sets it
  in `bridgeInitialize` behind a proxy; `onlyNTV`'s zero-vault legacy fallback is
  therefore unreachable here and is not transcribed.
* No initializer, metadata, allowance/permit, reinitializer, `ERC1967Upgrade`
  surface, or storage-layout compatibility.  The test adapter deploys the
  original behind a `BeaconProxy` and initializes it from the vault address.
* The empty `_beforeTokenTransfer`/`_afterTokenTransfer` hooks are omitted.
-/

namespace Codegen.BridgedTokenSlice

open Codegen

def zeroAddr : Expr := .lit .address 0

/-- `onlyNTV`, nonzero-vault branch: `require(msg.sender == ntv, Unauthorized(msg.sender))`. -/
def onlyNTV : Stmt :=
  .require (.eq .sender (.sload "_nativeTokenVault")) (.custom "Unauthorized" [.sender])

def bridgeMint : Fn where
  name := "bridgeMint"
  params := [⟨"_to", .address⟩, ⟨"_amount", .uint256⟩]
  returns := none
  mutability := .nonpayable
  body :=
    [ onlyNTV,
      .require (.ne (.var "_to") zeroAddr) (.message "ERC20: mint to the zero address"),
      .sstore "_totalSupply" (.add true (.sload "_totalSupply") (.var "_amount")),
      .mstore "_balances" (.var "_to")
        (.add false (.mload "_balances" (.var "_to")) (.var "_amount")),
      .emit "Transfer" [zeroAddr, .var "_to", .var "_amount"],
      .emit "BridgeMint" [.var "_to", .var "_amount"] ]

def bridgeBurn : Fn where
  name := "bridgeBurn"
  params := [⟨"_from", .address⟩, ⟨"_amount", .uint256⟩]
  returns := none
  mutability := .nonpayable
  body :=
    [ onlyNTV,
      .require (.ne (.var "_from") zeroAddr) (.message "ERC20: burn from the zero address"),
      .local_ .uint256 "accountBalance" (.mload "_balances" (.var "_from")),
      .require (.ge (.var "accountBalance") (.var "_amount"))
        (.message "ERC20: burn amount exceeds balance"),
      .mstore "_balances" (.var "_from") (.sub false (.var "accountBalance") (.var "_amount")),
      .sstore "_totalSupply" (.sub false (.sload "_totalSupply") (.var "_amount")),
      .emit "Transfer" [.var "_from", zeroAddr, .var "_amount"],
      .emit "BridgeBurn" [.var "_from", .var "_amount"] ]

/-- `transfer(to, amount)` with `owner = msg.sender`.  The recipient balance is
read *after* the debit, as in OZ, which is what makes a self-transfer an identity. -/
def transfer : Fn where
  name := "transfer"
  params := [⟨"to", .address⟩, ⟨"amount", .uint256⟩]
  returns := some .bool
  mutability := .nonpayable
  body :=
    [ .require (.ne .sender zeroAddr) (.message "ERC20: transfer from the zero address"),
      .require (.ne (.var "to") zeroAddr) (.message "ERC20: transfer to the zero address"),
      .local_ .uint256 "fromBalance" (.mload "_balances" .sender),
      .require (.ge (.var "fromBalance") (.var "amount"))
        (.message "ERC20: transfer amount exceeds balance"),
      .mstore "_balances" .sender (.sub false (.var "fromBalance") (.var "amount")),
      .mstore "_balances" (.var "to") (.add false (.mload "_balances" (.var "to")) (.var "amount")),
      .emit "Transfer" [.sender, .var "to", .var "amount"],
      .ret (.lit .bool 1) ]

def balanceOf : Fn where
  name := "balanceOf"
  params := [⟨"account", .address⟩]
  returns := some .uint256
  mutability := .view
  body := [.ret (.mload "_balances" (.var "account"))]

def totalSupply : Fn where
  name := "totalSupply"
  params := []
  returns := some .uint256
  mutability := .view
  body := [.ret (.sload "_totalSupply")]

def nativeTokenVault : Fn where
  name := "nativeTokenVault"
  params := []
  returns := some .address
  mutability := .view
  body := [.ret (.sload "_nativeTokenVault")]

def program : Contract where
  name := "BridgedTokenSlice"
  scalars := [⟨"_nativeTokenVault", .address⟩, ⟨"_totalSupply", .uint256⟩]
  maps := [("_balances", .address, .uint256)]
  errors := [⟨"Unauthorized", [⟨"caller", .address⟩]⟩, ⟨"ZeroAddress", []⟩]
  events :=
    [ ⟨"Transfer", [⟨"from", .address, true⟩, ⟨"to", .address, true⟩, ⟨"value", .uint256, false⟩]⟩,
      ⟨"BridgeMint", [⟨"account", .address, true⟩, ⟨"amount", .uint256, false⟩]⟩,
      ⟨"BridgeBurn", [⟨"account", .address, true⟩, ⟨"amount", .uint256, false⟩]⟩ ]
  ctorParams := [⟨"vault", .address⟩]
  ctorBody :=
    [ .require (.ne (.var "vault") zeroAddr) (.custom "ZeroAddress" []),
      .sstore "_nativeTokenVault" (.var "vault") ]
  fns := [bridgeMint, bridgeBurn, transfer, balanceOf, totalSupply, nativeTokenVault]

end Codegen.BridgedTokenSlice
