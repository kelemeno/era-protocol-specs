// SPDX-License-Identifier: MIT
// GENERATED from `Codegen.BridgedTokenSlice.program` by EraSpec/Codegen/Emit.lean. Do not edit:
// regenerate with scripts/emit-solidity.sh, which also checks this file is current.
pragma solidity 0.8.28;

contract BridgedTokenSlice {
    error Unauthorized(address caller);
    error ZeroAddress();
    event Transfer(address indexed from, address indexed to, uint256 value);
    event BridgeMint(address indexed account, uint256 amount);
    event BridgeBurn(address indexed account, uint256 amount);

    address internal _nativeTokenVault;
    uint256 internal _totalSupply;
    mapping(address => uint256) internal _balances;

    constructor(address vault) {
        require(vault != address(0), ZeroAddress());
        _nativeTokenVault = vault;
    }

    function bridgeMint(address _to, uint256 _amount) external {
        require(msg.sender == _nativeTokenVault, Unauthorized(msg.sender));
        require(_to != address(0), "ERC20: mint to the zero address");
        _totalSupply = (_totalSupply + _amount);
        unchecked { _balances[_to] = (_balances[_to] + _amount); }
        emit Transfer(address(0), _to, _amount);
        emit BridgeMint(_to, _amount);
    }

    function bridgeBurn(address _from, uint256 _amount) external {
        require(msg.sender == _nativeTokenVault, Unauthorized(msg.sender));
        require(_from != address(0), "ERC20: burn from the zero address");
        uint256 accountBalance = _balances[_from];
        require(accountBalance >= _amount, "ERC20: burn amount exceeds balance");
        unchecked { _balances[_from] = (accountBalance - _amount); }
        unchecked { _totalSupply = (_totalSupply - _amount); }
        emit Transfer(_from, address(0), _amount);
        emit BridgeBurn(_from, _amount);
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(msg.sender != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");
        uint256 fromBalance = _balances[msg.sender];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked { _balances[msg.sender] = (fromBalance - amount); }
        unchecked { _balances[to] = (_balances[to] + amount); }
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function balanceOf(address account) external view returns (uint256) {
        return _balances[account];
    }

    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    function nativeTokenVault() external view returns (address) {
        return _nativeTokenVault;
    }
}
