// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import { EncryptedERC } from "EncryptedERC/contracts/EncryptedERC.sol";
import { CreateEncryptedERCParams } from "EncryptedERC/contracts/types/Types.sol";

contract MyEncryptedToken is EncryptedERC {
    constructor(
        string memory _name,
        string memory _symbol,
        uint8 _decimals,
        address _registrar,
        address _allPurposeVerifier
    )
        EncryptedERC(
            CreateEncryptedERCParams({
                isConverter: false,
                registrar: _registrar,
                mintVerifier: _allPurposeVerifier,
                withdrawVerifier: _allPurposeVerifier,
                transferVerifier: _allPurposeVerifier,
                burnVerifier: _allPurposeVerifier,
                name: _name,
                symbol: _symbol,
                decimals: _decimals
            })
        )
    {}
}
