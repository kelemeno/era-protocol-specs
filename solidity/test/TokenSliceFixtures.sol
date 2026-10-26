// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {Test} from "forge-std/Test.sol";
import {ERC1967Proxy} from "@openzeppelin/contracts-v4/proxy/ERC1967/ERC1967Proxy.sol";
import {BridgedStandardERC20} from "era-contracts/bridge/BridgedStandardERC20.sol";
import {DataEncoding} from "era-contracts/common/libraries/DataEncoding.sol";
import {BridgedTokenSlice} from "../src/generated/BridgedTokenSlice.sol";
import {Vm} from "forge-std/Vm.sol";

/// @notice The interface both implementations are compared through: exactly the
///         generated slice's external surface.
interface ITokenSlice {
    function bridgeMint(address _to, uint256 _amount) external;
    function bridgeBurn(address _from, uint256 _amount) external;
    function transfer(address to, uint256 amount) external returns (bool);
    function balanceOf(address account) external view returns (uint256);
    function totalSupply() external view returns (uint256);
    function nativeTokenVault() external view returns (address);
}

/// @notice Deployment is the one place the implementations differ, and the only
///         thing an adapter normalizes (CODE_GENERATION.md, "One suite, two
///         implementations"). Authority, amounts, recipients and revert data are
///         compared unnormalized.
library TokenSliceDeploy {
    /// @dev The original behind an ERC1967 proxy, initialized from the vault — the
    ///      fixture of upstream's BridgedStandardERC20Additional.t.sol at the pin,
    ///      except that the initializing caller (hence the vault) is a parameter.
    function original(address vault) internal returns (address token) {
        BridgedStandardERC20 implementation = new BridgedStandardERC20();
        token = address(new ERC1967Proxy(address(implementation), bytes("")));
        bytes memory data = DataEncoding.encodeTokenData({
            _chainId: 1,
            _name: abi.encode("TestToken"),
            _symbol: abi.encode("TT"),
            _decimals: abi.encode(uint8(18))
        });
        VM.prank(vault);
        BridgedStandardERC20(token).bridgeInitialize(keccak256("assetId"), address(0xBEEF), data);
    }

    function generated(address vault) internal returns (address token) {
        token = address(new BridgedTokenSlice(vault));
    }

    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
}

/// @notice One suite, parameterized by implementation.
abstract contract TokenSliceFixture is Test {
    function deployToken(address vault) internal virtual returns (address);
    function implementationName() internal pure virtual returns (string memory);
}

abstract contract OriginalFixture is TokenSliceFixture {
    function deployToken(address vault) internal override returns (address) {
        return TokenSliceDeploy.original(vault);
    }

    function implementationName() internal pure override returns (string memory) {
        return "original";
    }
}

abstract contract GeneratedFixture is TokenSliceFixture {
    function deployToken(address vault) internal override returns (address) {
        return TokenSliceDeploy.generated(vault);
    }

    function implementationName() internal pure override returns (string memory) {
        return "generated";
    }
}
