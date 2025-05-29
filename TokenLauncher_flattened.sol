// SPDX-License-Identifier: MIT
pragma solidity =0.8.27 ^0.8.20;

// lib/openzeppelin-contracts/contracts/utils/Context.sol

// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

// lib/EncryptedERC/contracts/errors/Errors.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

error UserAlreadyRegistered();
error UserNotRegistered();
error UnauthorizedAccess();
error AuditorKeyNotSet();
error InvalidProof();
error InvalidOperation();
error TransferFailed();
error UnknownToken();
error InvalidChainId();
error InvalidNullifier();
error InvalidSender();
error InvalidRegistrationHash();
error ZeroAddress();
error TokenBlacklisted(address token);

// lib/EncryptedERC/contracts/interfaces/verifiers/IBurnVerifier.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

interface IBurnVerifier {
    function verifyProof(
        uint256[2] memory pointA_,
        uint256[2][2] memory pointB_,
        uint256[2] memory pointC_,
        uint256[19] memory publicSignals_
    ) external view returns (bool verified_);
}

// lib/openzeppelin-contracts/contracts/utils/introspection/IERC165.sol

// OpenZeppelin Contracts (last updated v5.1.0) (utils/introspection/IERC165.sol)

/**
 * @dev Interface of the ERC-165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[ERC].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[ERC section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

// lib/openzeppelin-contracts/contracts/token/ERC20/IERC20.sol

// OpenZeppelin Contracts (last updated v5.1.0) (token/ERC20/IERC20.sol)

/**
 * @dev Interface of the ERC-20 standard as defined in the ERC.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the value of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the value of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 value) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the
     * allowance mechanism. `value` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 value) external returns (bool);
}

// lib/EncryptedERC/contracts/interfaces/verifiers/IMintVerifier.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

interface IMintVerifier {
    function verifyProof(
        uint256[2] memory pointA_,
        uint256[2][2] memory pointB_,
        uint256[2] memory pointC_,
        uint256[24] memory publicSignals_
    ) external view returns (bool verified_);
}

// lib/EncryptedERC/contracts/interfaces/IRegistrar.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

interface IRegistrar {
    /**
     * @dev Returns the public key of a user.
     * @param user Address of the user.
     * @return publicKey The public key of the user as an array of two uint256 values.
     */
    function getUserPublicKey(
        address user
    ) external view returns (uint256[2] memory publicKey);

    /**
     * @dev Returns true if the user is registered.
     * @param user Address of the user.
     * @return isRegistered True if the user is registered, false otherwise.
     */
    function isUserRegistered(address user) external view returns (bool);
}

// lib/EncryptedERC/contracts/interfaces/verifiers/ITransferVerifier.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

interface ITransferVerifier {
    function verifyProof(
        uint256[2] memory pointA_,
        uint256[2][2] memory pointB_,
        uint256[2] memory pointC_,
        uint256[32] memory publicSignals_
    ) external view returns (bool verified_);
}

// lib/EncryptedERC/contracts/interfaces/verifiers/IWithdrawVerifier.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

interface IWithdrawVerifier {
    function verifyProof(
        uint256[2] memory pointA_,
        uint256[2][2] memory pointB_,
        uint256[2] memory pointC_,
        uint256[16] memory publicSignals_
    ) external view returns (bool verified_);
}

// lib/EncryptedERC/contracts/types/Types.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

struct Point {
    uint256 x;
    uint256 y;
}

struct CreateEncryptedERCParams {
    // registrar contract address for fetching users public key
    address registrar;
    // eERC is converter mode or not
    bool isConverter;
    // eERC Token
    string name;
    string symbol;
    uint8 decimals;
    // verifiers
    address mintVerifier;
    address withdrawVerifier;
    address transferVerifier;
    address burnVerifier;
}

struct AmountPCT {
    uint256[7] pct;
    uint256 index;
}

struct EncryptedBalance {
    EGCT eGCT;
    mapping(uint256 index => BalanceHistory history) balanceList;
    uint256 nonce;
    uint256 transactionIndex;
    uint256[7] balancePCT; // user balance pcts
    AmountPCT[] amountPCTs; // user amount pcts
}

struct BalanceHistory {
    uint256 index;
    bool isValid;
}

struct EGCT {
    Point c1;
    Point c2;
}

/// @dev The proof base is used to verify the proof
struct ProofPoints {
    uint256[2] a;
    uint256[2][2] b;
    uint256[2] c;
}

struct RegisterProof {
    ProofPoints proofPoints;
    uint256[5] publicSignals;
}

struct MintProof {
    ProofPoints proofPoints;
    uint256[24] publicSignals;
}

struct TransferProof {
    ProofPoints proofPoints;
    uint256[32] publicSignals;
}

struct BurnProof {
    ProofPoints proofPoints;
    uint256[19] publicSignals;
}

struct WithdrawProof {
    ProofPoints proofPoints;
    uint256[16] publicSignals;
}

struct TransferInputs {
    EGCT providedBalance;
    EGCT senderEncryptedAmount;
    EGCT receiverEncryptedAmount;
    uint256[7] amountPCT;
}

// lib/EncryptedERC/contracts/libraries/BabyJubJub.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Structs

/**
 * @dev BabyJubJub curve operations
 */
library BabyJubJub {
    // Curve parameters
    // E: A^2 + y^2 = 1 + Dx^2y^2 (mod Q)
    uint256 internal constant A = 168700;
    uint256 internal constant D = 168696;
    uint256 public constant Q =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant H =
        10944121435919637611123202872628637544274182200208017171849102093287904247808;
    uint256 internal constant R =
        2736030358979909402780800718157159386076813972158567259200215660948447373041;

    /**
     * @dev Subtract a BabyJubJub point from another BabyJubJub point
     * @param _point1 the point which will be subtracted from
     * @param _point2 point to subtract
     * @return result
     */
    function _sub(
        Point memory _point1,
        Point memory _point2
    ) public view returns (Point memory) {
        return _add(_point1, negate(_point2));
    }

    /**
     * @dev Add 2 points on BabyJubJub curve
     * Formulae for adding 2 points on a twisted Edwards curve:
     * x3 = (x1y2 + y1x2) / (1 + dx1x2y1y2)
     * y3 = (y1y2 - ax1x2) / (1 - dx1x2y1y2)
     * @param _point1 first point
     * @param _point2 second point
     * @return resulting point
     */
    function _add(
        Point memory _point1,
        Point memory _point2
    ) public view returns (Point memory) {
        uint256 x1x2 = mulmod(_point1.x, _point2.x, Q);
        uint256 y1y2 = mulmod(_point1.y, _point2.y, Q);

        uint256 dx1x2y1y2 = mulmod(D, mulmod(x1x2, y1y2, Q), Q);

        uint256 x3Num = addmod(
            mulmod(_point1.x, _point2.y, Q),
            mulmod(_point1.y, _point2.x, Q),
            Q
        );
        uint256 y3Num = submod(y1y2, mulmod(A, x1x2, Q));

        return
            Point({
                x: mulmod(x3Num, invmod(addmod(1, dx1x2y1y2, Q)), Q),
                y: mulmod(y3Num, invmod(submod(1, dx1x2y1y2)), Q)
            });
    }

    /**
     * @dev Multiply a BabyJubJub point by a scalar
     * Use the double and add algorithm
     * @param _point point be multiplied by a scalar
     * @param _scalar scalar value
     * @return resulting point
     */
    function scalarMultiply(
        Point memory _point,
        uint256 _scalar
    ) public view returns (Point memory) {
        // Initial scalar remainder
        uint256 remaining = _scalar % R;

        // Copy initial point so that we don't mutate it
        Point memory initial = _point;

        // Initialize result
        Point memory result = Point({x: 0, y: 1});

        // Loop while remainder is greater than 0
        while (remaining != 0) {
            // If the right-most binary digit is 1 (number is odd) add initial point to result
            if ((remaining & 1) != 0) {
                result = _add(result, initial);
            }

            // Double initial point
            initial = double(initial);

            // Shift bits to the right
            remaining = remaining >> 1;
        }

        return result;
    }

    /**
     *
     * @param _publicKey Public Key that will be used in encryption
     * @param _msg Message in scalar form to be encrypted
     */
    function elGamalEncryption(
        Point memory _publicKey,
        uint256 _msg
    ) public view returns (EGCT memory) {
        uint256 random = 1;
        Point memory b8 = base8();

        Point memory c1 = scalarMultiply(b8, random);
        Point memory pkr = scalarMultiply(_publicKey, random);
        Point memory pMsg = scalarMultiply(b8, _msg);

        Point memory c2 = _add(pkr, pMsg);

        return EGCT({c1: c1, c2: c2});
    }

    // elgamal encryption with a given message
    function encrypt(
        Point memory _publicKey,
        uint256 _msg
    ) public view returns (EGCT memory) {
        return elGamalEncryption(_publicKey, _msg);
    }

    /**
     * @dev Default generator
     */
    function base8() public pure returns (Point memory) {
        return
            Point({
                x: 5299619240641551281634865583518297030282874472190772894086521144482721001553,
                y: 16950150798460657717958625567821834550301663161624707787222815936182638968203
            });
    }

    /**
     * @dev Double a point on BabyJubJub curve
     * @param _p point to double
     * @return doubled point
     */
    function double(Point memory _p) internal view returns (Point memory) {
        return _add(_p, _p);
    }

    /**
     * @dev Compute modular inverse of a number
     * @param _a the value to be inverted in mod Q
     */
    function invmod(uint256 _a) internal view returns (uint256) {
        // We can use Euler's theorem instead of the extended Euclidean algorithm
        // Since m = Q and Q is prime we have: a^-1 = a^(m - 2) (mod m)
        return
            expmod(
                _a,
                0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593efffffff
            );
    }

    /**
     * @dev Exponentiation modulo Q
     * @param _base the base of the exponentiation
     * @param _exponent the exponent
     * @return result
     */
    function expmod(
        uint256 _base,
        uint256 _exponent
    ) internal view returns (uint256) {
        uint256 result;

        // solhint-disable-next-line no-inline-assembly
        assembly {
            let
                localQ
            := 0x30644E72E131A029B85045B68181585D2833E84879B9709143E1F593F0000001
            let memPtr := mload(0x40)
            mstore(memPtr, 0x20) // Length of base _b
            mstore(add(memPtr, 0x20), 0x20) // Length of exponent _e
            mstore(add(memPtr, 0x40), 0x20) // Length of modulus Q
            mstore(add(memPtr, 0x60), _base) // Base _b
            mstore(add(memPtr, 0x80), _exponent) // Exponent _e
            mstore(add(memPtr, 0xa0), localQ) // Modulus Q

            // The bigModExp precompile is at 0x05
            let success := staticcall(gas(), 0x05, memPtr, 0xc0, memPtr, 0x20)
            switch success
            case 0 {
                revert(0x0, 0x0)
            }
            default {
                result := mload(memPtr)
            }
        }

        return result;
    }

    /**
     * @dev Negate a BabyJubJub point
     * @param _point point to negate
     * @return p = -(_p)
     */
    function negate(Point memory _point) internal pure returns (Point memory) {
        return Point({x: Q - _point.x, y: _point.y});
    }

    /**
     * @dev Modular subtract (mod n).
     * @param _a The first number
     * @param _b The number to be subtracted
     * @return result
     */
    function submod(uint256 _a, uint256 _b) internal pure returns (uint256) {
        return addmod(_a, Q - _b, Q);
    }
}

// lib/openzeppelin-contracts/contracts/interfaces/IERC165.sol

// OpenZeppelin Contracts (last updated v5.0.0) (interfaces/IERC165.sol)

// lib/openzeppelin-contracts/contracts/interfaces/IERC20.sol

// OpenZeppelin Contracts (last updated v5.0.0) (interfaces/IERC20.sol)

// lib/openzeppelin-contracts/contracts/token/ERC20/extensions/IERC20Metadata.sol

// OpenZeppelin Contracts (last updated v5.1.0) (token/ERC20/extensions/IERC20Metadata.sol)

/**
 * @dev Interface for the optional metadata functions from the ERC-20 standard.
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

// lib/openzeppelin-contracts/contracts/access/Ownable.sol

// OpenZeppelin Contracts (last updated v5.0.0) (access/Ownable.sol)

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * The initial owner is set to the address provided by the deployer. This can
 * later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    /**
     * @dev The caller account is not authorized to perform an operation.
     */
    error OwnableUnauthorizedAccount(address account);

    /**
     * @dev The owner is not a valid owner account. (eg. `address(0)`)
     */
    error OwnableInvalidOwner(address owner);

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the address provided by the deployer as the initial owner.
     */
    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(initialOwner);
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        if (owner() != _msgSender()) {
            revert OwnableUnauthorizedAccount(_msgSender());
        }
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        if (newOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// lib/EncryptedERC/contracts/auditor/AuditorManager.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

/**
 * @title AuditorManager
 * @notice Abstract contract that manages auditor-related functionality for encrypted ERC operations
 * @dev This contract is responsible for:
 *      1. Storing and managing the auditor's address and public key
 *      2. Providing access control for auditor-related operations
 *      3. Emitting events when auditor information changes
 *
 * The auditor is a crucial component in the encrypted ERC system that:
 * - Ensures compliance with regulatory requirements
 * - Provides oversight for private operations
 */
abstract contract AuditorManager {
    ///////////////////////////////////////////////////
    ///                   State Variables           ///
    ///////////////////////////////////////////////////

    /// @notice The address of the current auditor
    /// @dev This address is used to identify the auditor and for access control
    address public auditor = address(0);

    /// @notice The public key of the current auditor
    /// @dev This is used in zero-knowledge proofs to validate auditor signatures
    ///      The point (0,1) is considered invalid as it's the identity point in the elliptic curve
    Point public auditorPublicKey = Point({x: 0, y: 0});

    ///////////////////////////////////////////////////
    ///                    Events                   ///
    ///////////////////////////////////////////////////

    /**
     * @notice Emitted when the auditor's information is updated
     * @param oldAuditor The previous auditor's address
     * @param newAuditor The new auditor's address
     */
    event AuditorChanged(
        address indexed oldAuditor,
        address indexed newAuditor
    );

    ///////////////////////////////////////////////////
    ///                   Modifiers                 ///
    ///////////////////////////////////////////////////

    /**
     * @notice Ensures that an auditor is properly
     * @dev This modifier checks two conditions:
     *      1. The auditor's public key is valid (not the identity point)
     *      2. The auditor's address is not the zero address
     *
     * Requirements:
     * - Auditor public key must be set (not the identity point)
     * - Auditor address must be set (not zero address)
     */
    modifier onlyIfAuditorSet() {
        require(
            auditorPublicKey.x != 0 && auditorPublicKey.y != 1,
            "Auditor public key not set"
        );
        require(auditor != address(0), "Auditor not set");
        _;
    }

    ///////////////////////////////////////////////////
    ///                   External                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Checks if the auditor's public key is properly set
     * @return bool True if the auditor's public key is set and valid
     * @dev This function is used to verify if the contract is ready for
     *      operations that require auditor validation
     */
    function isAuditorKeySet() external view returns (bool) {
        return auditorPublicKey.x != 0 && auditorPublicKey.y != 1;
    }

    ///////////////////////////////////////////////////
    ///                   Internal                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Updates the auditor's information
     * @param newAuditor The address of the new auditor
     * @param publicKey The public key of the new auditor
     * @dev This function:
     *      1. Validates the new auditor's address
     *      2. Updates the auditor's information
     *      3. Emits an event to track the change
     *
     * Requirements:
     * - newAuditor must not be the zero address
     * - publicKey must be a valid point on the elliptic curve
     */
    function _updateAuditor(
        address newAuditor,
        uint256[2] memory publicKey
    ) internal {
        address oldAuditor = auditor;
        // check if the auditor is the zero address
        if (newAuditor == address(0)) {
            revert ZeroAddress();
        }

        auditor = newAuditor;
        auditorPublicKey = Point({x: publicKey[0], y: publicKey[1]});

        emit AuditorChanged(oldAuditor, newAuditor);
    }
}

// lib/openzeppelin-contracts/contracts/access/Ownable2Step.sol

// OpenZeppelin Contracts (last updated v5.1.0) (access/Ownable2Step.sol)

/**
 * @dev Contract module which provides access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * This extension of the {Ownable} contract includes a two-step mechanism to transfer
 * ownership, where the new owner must call {acceptOwnership} in order to replace the
 * old one. This can help prevent common mistakes, such as transfers of ownership to
 * incorrect accounts, or to contracts that are unable to interact with the
 * permission system.
 *
 * The initial owner is specified at deployment time in the constructor for `Ownable`. This
 * can later be changed with {transferOwnership} and {acceptOwnership}.
 *
 * This module is used through inheritance. It will make available all functions
 * from parent (Ownable).
 */
abstract contract Ownable2Step is Ownable {
    address private _pendingOwner;

    event OwnershipTransferStarted(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Returns the address of the pending owner.
     */
    function pendingOwner() public view virtual returns (address) {
        return _pendingOwner;
    }

    /**
     * @dev Starts the ownership transfer of the contract to a new account. Replaces the pending transfer if there is one.
     * Can only be called by the current owner.
     *
     * Setting `newOwner` to the zero address is allowed; this can be used to cancel an initiated ownership transfer.
     */
    function transferOwnership(address newOwner) public virtual override onlyOwner {
        _pendingOwner = newOwner;
        emit OwnershipTransferStarted(owner(), newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`) and deletes any pending owner.
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual override {
        delete _pendingOwner;
        super._transferOwnership(newOwner);
    }

    /**
     * @dev The new owner accepts the ownership transfer.
     */
    function acceptOwnership() public virtual {
        address sender = _msgSender();
        if (pendingOwner() != sender) {
            revert OwnableUnauthorizedAccount(sender);
        }
        _transferOwnership(sender);
    }
}

// lib/EncryptedERC/contracts/EncryptedUserBalances.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

/**
 * @title EncryptedUserBalances
 * @notice Contract for managing encrypted user balances in the privacy-preserving ERC system
 * @dev This contract handles:
 *      1. Storage and retrieval of encrypted balances
 *      2. Balance history tracking for transaction validation
 *      3. Cryptographic operations on encrypted balances
 *
 * The contract uses ElGamal encryption (EGCT) to store balances privately,
 * allowing users to prove they have sufficient funds without revealing the actual amount.
 */
contract EncryptedUserBalances {
    ///////////////////////////////////////////////////
    ///                   State Variables           ///
    ///////////////////////////////////////////////////

    /// @notice Mapping of user addresses to their encrypted balances for each token
    /// @dev Structure: user => tokenId => EncryptedBalance
    mapping(address user => mapping(uint256 tokenId => EncryptedBalance balance))
        public balances;

    ///////////////////////////////////////////////////
    ///                   External                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Returns the encrypted balance for a user's standalone token
     * @param user The address of the user
     * @return eGCT The ElGamal ciphertext representing the encrypted balance
     * @return nonce The current nonce used for balance validation
     * @return amountPCTs Array of amount PCT
     * @return balancePCT The current balance PCT
     * @return transactionIndex The current transaction index
     * @dev Since in standalone mode, the tokenId is always 0
     */
    function balanceOfStandalone(
        address user
    )
        external
        view
        returns (
            EGCT memory eGCT,
            uint256 nonce,
            AmountPCT[] memory amountPCTs,
            uint256[7] memory balancePCT,
            uint256 transactionIndex
        )
    {
        return balanceOf(user, 0);
    }

    /**
     * @notice Returns the encrypted balance for a user's specified token
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @return eGCT The ElGamal ciphertext representing the encrypted balance
     * @return nonce The current nonce used for balance validation
     * @return amountPCTs Array of amount PCT
     * @return balancePCT The current balance PCT
     * @return transactionIndex The current transaction index
     */
    function balanceOf(
        address user,
        uint256 tokenId
    )
        public
        view
        returns (
            EGCT memory eGCT,
            uint256 nonce,
            AmountPCT[] memory amountPCTs,
            uint256[7] memory balancePCT,
            uint256 transactionIndex
        )
    {
        EncryptedBalance storage balance = balances[user][tokenId];
        return (
            balance.eGCT,
            balance.nonce,
            balance.amountPCTs,
            balance.balancePCT,
            balance.transactionIndex
        );
    }

    ///////////////////////////////////////////////////
    ///                   Internal                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Adds an encrypted amount to a user's balance
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @param eGCT The ElGamal ciphertext representing the amount to add
     * @param amountPCT The amount PCT for transaction history
     * @dev This function:
     *      1. Initializes the balance if it's the first transaction
     *      2. Adds the encrypted amount to the existing balance
     *      3. Updates the user history (by adding new amount PCT)
     */
    function _addToUserBalance(
        address user,
        uint256 tokenId,
        EGCT memory eGCT,
        uint256[7] memory amountPCT
    ) internal {
        EncryptedBalance storage balance = balances[user][tokenId];

        // if user balance is not initialized, initialize it
        if (balance.eGCT.c1.x == 0 && balance.eGCT.c1.y == 0) {
            balance.eGCT = eGCT;
        } else {
            // if user balance is already initialized, add the encrypted amount to the balance
            balance.eGCT.c1 = BabyJubJub._add(balance.eGCT.c1, eGCT.c1);
            balance.eGCT.c2 = BabyJubJub._add(balance.eGCT.c2, eGCT.c2);
        }

        // in all the case
        _addToUserHistory(user, tokenId, amountPCT);
    }

    /**
     * @notice Subtracts an encrypted amount from a user's balance
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @param eGCT The ElGamal ciphertext representing the amount to subtract
     * @param balancePCT The new balance PCT after subtraction
     * @param transactionIndex The transaction index to delete from history
     * @dev This function:
     *      1. Subtracts the encrypted amount from the balance
     *      2. Updates the user history (by removing the specified transaction)
     *      3. Updates the balance PCT for user
     */
    function _subtractFromUserBalance(
        address user,
        uint256 tokenId,
        EGCT memory eGCT,
        uint256[7] memory balancePCT,
        uint256 transactionIndex
    ) internal {
        EncryptedBalance storage balance = balances[user][tokenId];

        balance.eGCT.c1 = BabyJubJub._sub(balance.eGCT.c1, eGCT.c1);
        balance.eGCT.c2 = BabyJubJub._sub(balance.eGCT.c2, eGCT.c2);

        // delete the amount pct from the balance
        _deleteUserHistory(user, tokenId, transactionIndex);

        // update balance pct
        balance.balancePCT = balancePCT;
    }

    /**
     * @notice Adds a transaction to the user's balance history
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @param amountPCT The amount PCT for the transaction
     * @dev This function:
     *      1. Calculates a unique hash for the current balance state
     *      2. Marks this hash as valid in the balance history
     *      3. Adds the amount PCT to the transaction history
     *      4. Increments the transaction index
     *
     * The balance hash is unique for each transaction because it includes the nonce,
     * which is incremented after each transaction. This ensures that each transaction
     * can be uniquely identified and validated.
     */
    function _addToUserHistory(
        address user,
        uint256 tokenId,
        uint256[7] memory amountPCT
    ) internal {
        EncryptedBalance storage balance = balances[user][tokenId];

        uint256 nonce = balance.nonce;
        uint256 balanceHash = _hashEGCT(balance.eGCT);
        balanceHash = uint256(keccak256(abi.encode(balanceHash, nonce)));

        // mark the balance hash as valid
        balance.balanceList[balanceHash] = BalanceHistory({
            index: balance.transactionIndex,
            isValid: true
        });

        // add the amount pct to the balance
        balance.amountPCTs.push(
            AmountPCT({pct: amountPCT, index: balance.transactionIndex})
        );

        balance.transactionIndex++;
    }

    /**
     * @notice Commits the current balance state to the user's history
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @dev This function:
     *      1. Calculates a unique hash for the current balance state
     *      2. Marks this hash as valid in the balance history
     *      3. Increments the transaction index
     *
     * This is used to create a checkpoint of the balance state after operations
     * that don't change the balance amount but need to be recorded in history.
     */
    function _commitUserBalance(address user, uint256 tokenId) internal {
        EncryptedBalance storage balance = balances[user][tokenId];

        uint256 nonce = balance.nonce;
        uint256 balanceHash = _hashEGCT(balance.eGCT);
        balanceHash = uint256(keccak256(abi.encode(balanceHash, nonce)));

        balance.balanceList[balanceHash] = BalanceHistory({
            index: balance.transactionIndex,
            isValid: true
        });

        balance.transactionIndex++;
    }

    /**
     * @notice Deletes transaction history up to a specific transaction index
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @param transactionIndex The transaction index to delete up to
     * @dev This function:
     *      1. Removes amount PCTs from the history up to the specified index
     *      2. Increments the nonce (invalidate all previous balance hashes)
     *      3. Commits the new balance state to history
     *
     * Instead of deleting individual history entries, this function uses the nonce
     * to invalidate all previous balance hashes at once, which is more gas efficient.
     */
    function _deleteUserHistory(
        address user,
        uint256 tokenId,
        uint256 transactionIndex
    ) internal {
        EncryptedBalance storage balance = balances[user][tokenId];

        for (uint256 i = balance.amountPCTs.length; i > 0; i--) {
            uint256 index = i - 1;

            if (balance.amountPCTs[index].index <= transactionIndex) {
                balance.amountPCTs[index] = balance.amountPCTs[
                    balance.amountPCTs.length - 1
                ];
                balance.amountPCTs.pop();
            }
        }

        balance.nonce++;

        _commitUserBalance(user, tokenId);
    }

    /**
     * @notice Checks if a balance hash is valid for a user
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @param balanceHash The hash to validate
     * @return isValid True if the hash is valid, false otherwise
     * @return index The transaction index associated with the hash
     * This is used to validate that a user is using a recent and valid balance
     * in their transactions.
     */
    function _isBalanceValid(
        address user,
        uint256 tokenId,
        uint256 balanceHash
    ) internal view returns (bool, uint256) {
        uint256 nonce = balances[user][tokenId].nonce;
        uint256 hashWithNonce = uint256(
            keccak256(abi.encode(balanceHash, nonce))
        );
        return (
            balances[user][tokenId].balanceList[hashWithNonce].isValid,
            balances[user][tokenId].balanceList[hashWithNonce].index
        );
    }

    /**
     * @notice Verifies a user's balance
     * @param user The address of the user
     * @param tokenId The ID of the token
     * @param eGCT The ElGamal ciphertext representing the balance
     * @return transactionIndex The transaction index associated with the balance
     * @dev If balance is not valid, it reverts with InvalidProof error
     */
    function _verifyUserBalance(
        address user,
        uint256 tokenId,
        EGCT memory eGCT
    ) internal view returns (uint256) {
        // hash the encrypted balance
        uint256 balanceHash = _hashEGCT(eGCT);

        (bool isValid, uint256 transactionIndex) = _isBalanceValid(
            user,
            tokenId,
            balanceHash
        );
        if (!isValid) {
            revert InvalidProof();
        }

        return transactionIndex;
    }

    /**
     * @notice Calculates a hash of an ElGamal ciphertext
     * @param eGCT The ElGamal ciphertext to hash
     * @return The hash of the ciphertext
     * @dev This function creates a unique identifier for an encrypted balance
     *      by hashing all components of the ElGamal ciphertext.
     */
    function _hashEGCT(EGCT memory eGCT) internal pure returns (uint256) {
        return
            uint256(
                keccak256(
                    abi.encode(eGCT.c1.x, eGCT.c1.y, eGCT.c2.x, eGCT.c2.y)
                )
            );
    }
}

// lib/openzeppelin-contracts/contracts/interfaces/IERC1363.sol

// OpenZeppelin Contracts (last updated v5.1.0) (interfaces/IERC1363.sol)

/**
 * @title IERC1363
 * @dev Interface of the ERC-1363 standard as defined in the https://eips.ethereum.org/EIPS/eip-1363[ERC-1363].
 *
 * Defines an extension interface for ERC-20 tokens that supports executing code on a recipient contract
 * after `transfer` or `transferFrom`, or code on a spender contract after `approve`, in a single transaction.
 */
interface IERC1363 is IERC20, IERC165 {
    /*
     * Note: the ERC-165 identifier for this interface is 0xb0202a11.
     * 0xb0202a11 ===
     *   bytes4(keccak256('transferAndCall(address,uint256)')) ^
     *   bytes4(keccak256('transferAndCall(address,uint256,bytes)')) ^
     *   bytes4(keccak256('transferFromAndCall(address,address,uint256)')) ^
     *   bytes4(keccak256('transferFromAndCall(address,address,uint256,bytes)')) ^
     *   bytes4(keccak256('approveAndCall(address,uint256)')) ^
     *   bytes4(keccak256('approveAndCall(address,uint256,bytes)'))
     */

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferAndCall(address to, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @param data Additional data with no specified format, sent in call to `to`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferAndCall(address to, uint256 value, bytes calldata data) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param from The address which you want to send tokens from.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferFromAndCall(address from, address to, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param from The address which you want to send tokens from.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @param data Additional data with no specified format, sent in call to `to`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferFromAndCall(address from, address to, uint256 value, bytes calldata data) external returns (bool);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
     * @param spender The address which will spend the funds.
     * @param value The amount of tokens to be spent.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function approveAndCall(address spender, uint256 value) external returns (bool);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
     * @param spender The address which will spend the funds.
     * @param value The amount of tokens to be spent.
     * @param data Additional data with no specified format, sent in call to `spender`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function approveAndCall(address spender, uint256 value, bytes calldata data) external returns (bool);
}

// lib/EncryptedERC/contracts/tokens/TokenTracker.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

/**
 * @title TokenTracker
 * @notice Contract for tracking ERC20 tokens in the encrypted ERC system
 * @dev This contract manages:
 *      1. Token registration and identification
 *      2. Token blacklisting for security
 *      3. Contract Mode (converter vs standalone)
 *
 * The contract can operate in two modes:
 * - Converter Mode: Wraps existing ERC20 tokens into encrypted tokens
 * - Standalone Mode: Operates as a standalone encrypted token
 */
contract TokenTracker is Ownable2Step {
    ///////////////////////////////////////////////////
    ///                   State Variables           ///
    ///////////////////////////////////////////////////

    /// @notice The next available token ID
    /// @dev Token IDs start from 1, with 0 reserved for the standalone version
    uint256 public nextTokenId = 1;

    /// @notice Indicates if the contract is operating in converter mode
    bool public isConverter;

    /// @notice Mapping from token address to token ID
    mapping(address tokenAddress => uint256 tokenId) public tokenIds;

    /// @notice Mapping from token ID to token address
    mapping(uint256 tokenId => address tokenAddress) public tokenAddresses;

    /// @notice Array of all registered token addresses
    address[] public tokens;

    /// @notice Mapping to track blacklisted tokens
    mapping(address tokenAddress => bool isBlacklisted)
        public blacklistedTokens;

    ///////////////////////////////////////////////////
    ///                   Modifiers                 ///
    ///////////////////////////////////////////////////

    /**
     * @notice Ensures the function is only called in converter mode
     * @dev Reverts with InvalidOperation if called in standalone mode
     */
    modifier onlyForConverter() {
        if (!isConverter) {
            revert InvalidOperation();
        }
        _;
    }

    /**
     * @notice Ensures the function is only called in standalone mode
     * @dev Reverts with InvalidOperation if called in converter mode
     */
    modifier onlyForStandalone() {
        if (isConverter) {
            revert InvalidOperation();
        }
        _;
    }

    /**
     * @notice Ensures the token is not blacklisted
     * @param tokenAddress Address of the token to check
     * @dev Reverts with TokenBlacklisted if the token is blacklisted
     */
    modifier revertIfBlacklisted(address tokenAddress) {
        if (blacklistedTokens[tokenAddress]) {
            revert TokenBlacklisted(tokenAddress);
        }
        _;
    }

    ///////////////////////////////////////////////////
    ///                   Constructor               ///
    ///////////////////////////////////////////////////

    /**
     * @notice Initializes the TokenTracker contract
     * @param isConverter_ Determines if the contract operates in converter mode
     * @dev Sets the initial mode of operation and initializes the owner
     */
    constructor(bool isConverter_) Ownable(msg.sender) {
        isConverter = isConverter_;
    }

    ///////////////////////////////////////////////////
    ///                   External                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Sets the blacklist status of a token
     * @param token Address of the token to blacklist/unblacklist
     * @param blacklisted True to blacklist, false to unblacklist
     * @dev Only the owner can call this function
     */
    function setTokenBlacklist(
        address token,
        bool blacklisted
    ) external onlyOwner {
        blacklistedTokens[token] = blacklisted;
    }

    /**
     * @notice Returns an array of all registered token addresses
     * @return Array of token addresses
     * @dev Used for enumeration and listing all supported tokens
     */
    function getTokens() external view returns (address[] memory) {
        return tokens;
    }

    ///////////////////////////////////////////////////
    ///                   Internal                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Adds a new token to the tracker
     * @param tokenAddress Address of the token to add
     * @dev This function:
     *      1. Assigns a new token ID
     *      2. Updates the token mappings
     *      3. Adds the token to the tokens array
     *      4. Increments the next token ID
     */
    function _addToken(address tokenAddress) internal {
        uint256 newTokenId = nextTokenId;
        tokenIds[tokenAddress] = newTokenId;
        tokenAddresses[newTokenId] = tokenAddress;
        tokens.push(tokenAddress);
        nextTokenId++;
    }
}

// lib/openzeppelin-contracts/contracts/token/ERC20/utils/SafeERC20.sol

// OpenZeppelin Contracts (last updated v5.3.0) (token/ERC20/utils/SafeERC20.sol)

/**
 * @title SafeERC20
 * @dev Wrappers around ERC-20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    /**
     * @dev An operation with an ERC-20 token failed.
     */
    error SafeERC20FailedOperation(address token);

    /**
     * @dev Indicates a failed `decreaseAllowance` request.
     */
    error SafeERC20FailedDecreaseAllowance(address spender, uint256 currentAllowance, uint256 requestedDecrease);

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeCall(token.transfer, (to, value)));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeCall(token.transferFrom, (from, to, value)));
    }

    /**
     * @dev Variant of {safeTransfer} that returns a bool instead of reverting if the operation is not successful.
     */
    function trySafeTransfer(IERC20 token, address to, uint256 value) internal returns (bool) {
        return _callOptionalReturnBool(token, abi.encodeCall(token.transfer, (to, value)));
    }

    /**
     * @dev Variant of {safeTransferFrom} that returns a bool instead of reverting if the operation is not successful.
     */
    function trySafeTransferFrom(IERC20 token, address from, address to, uint256 value) internal returns (bool) {
        return _callOptionalReturnBool(token, abi.encodeCall(token.transferFrom, (from, to, value)));
    }

    /**
     * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     *
     * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
     * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
     * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
     * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
     */
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        forceApprove(token, spender, oldAllowance + value);
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `requestedDecrease`. If `token` returns no
     * value, non-reverting calls are assumed to be successful.
     *
     * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
     * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
     * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
     * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
     */
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 requestedDecrease) internal {
        unchecked {
            uint256 currentAllowance = token.allowance(address(this), spender);
            if (currentAllowance < requestedDecrease) {
                revert SafeERC20FailedDecreaseAllowance(spender, currentAllowance, requestedDecrease);
            }
            forceApprove(token, spender, currentAllowance - requestedDecrease);
        }
    }

    /**
     * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
     * to be set to zero before setting it to a non-zero value, such as USDT.
     *
     * NOTE: If the token implements ERC-7674, this function will not modify any temporary allowance. This function
     * only sets the "standard" allowance. Any temporary allowance will remain active, in addition to the value being
     * set here.
     */
    function forceApprove(IERC20 token, address spender, uint256 value) internal {
        bytes memory approvalCall = abi.encodeCall(token.approve, (spender, value));

        if (!_callOptionalReturnBool(token, approvalCall)) {
            _callOptionalReturn(token, abi.encodeCall(token.approve, (spender, 0)));
            _callOptionalReturn(token, approvalCall);
        }
    }

    /**
     * @dev Performs an {ERC1363} transferAndCall, with a fallback to the simple {ERC20} transfer if the target has no
     * code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * Reverts if the returned value is other than `true`.
     */
    function transferAndCallRelaxed(IERC1363 token, address to, uint256 value, bytes memory data) internal {
        if (to.code.length == 0) {
            safeTransfer(token, to, value);
        } else if (!token.transferAndCall(to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Performs an {ERC1363} transferFromAndCall, with a fallback to the simple {ERC20} transferFrom if the target
     * has no code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * Reverts if the returned value is other than `true`.
     */
    function transferFromAndCallRelaxed(
        IERC1363 token,
        address from,
        address to,
        uint256 value,
        bytes memory data
    ) internal {
        if (to.code.length == 0) {
            safeTransferFrom(token, from, to, value);
        } else if (!token.transferFromAndCall(from, to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Performs an {ERC1363} approveAndCall, with a fallback to the simple {ERC20} approve if the target has no
     * code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * NOTE: When the recipient address (`to`) has no code (i.e. is an EOA), this function behaves as {forceApprove}.
     * Opposedly, when the recipient address (`to`) has code, this function only attempts to call {ERC1363-approveAndCall}
     * once without retrying, and relies on the returned value to be true.
     *
     * Reverts if the returned value is other than `true`.
     */
    function approveAndCallRelaxed(IERC1363 token, address to, uint256 value, bytes memory data) internal {
        if (to.code.length == 0) {
            forceApprove(token, to, value);
        } else if (!token.approveAndCall(to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturnBool} that reverts if call fails to meet the requirements.
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            let success := call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0x20)
            // bubble errors
            if iszero(success) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0, returndatasize())
                revert(ptr, returndatasize())
            }
            returnSize := returndatasize()
            returnValue := mload(0)
        }

        if (returnSize == 0 ? address(token).code.length == 0 : returnValue != 1) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturn} that silently catches all reverts and returns a bool instead.
     */
    function _callOptionalReturnBool(IERC20 token, bytes memory data) private returns (bool) {
        bool success;
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            success := call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0x20)
            returnSize := returndatasize()
            returnValue := mload(0)
        }
        return success && (returnSize == 0 ? address(token).code.length > 0 : returnValue == 1);
    }
}

// lib/EncryptedERC/contracts/EncryptedERC.sol
// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// contracts

// libraries

// types

// errors

// interfaces

//             /$$$$$$$$ /$$$$$$$   /$$$$$$
//            | $$_____/| $$__  $$ /$$__  $$
//    /$$$$$$ | $$      | $$  \ $$| $$  \__/
//   /$$__  $$| $$$$$   | $$$$$$$/| $$  | $$
//  | $$_____/| $$      | $$  \ $$| $$  | $$
//  |  $$$$$$$| $$$$$$$$| $$  | $$|  $$$$$$/
//   \_______/|________/|__/  |__/ \______/
//
/**
 * @title EncryptedERC
 * @notice A privacy-preserving ERC20 token implementation that uses zero-knowledge proofs for managing balances in encrypted manner.
 * @dev This contract implements Encrypted ERC operations using zero-knowledge proofs.
 *
 * Key features:
 * - Encrypted ERC has 2 modes:
 *   - Standalone Mode: Act like a standalone ERC20 token (mint, burn, transfer)
 *   - Converter Mode: Wraps existing ERC20 tokens and encrypted ERC20 tokens (deposit, withdraw, transfer)
 * - Auditor Manager: Manages auditor's public key
 * - Token Tracker: Manages ERC20 token registration for deposit and withdrawal
 * - Encrypted User Balances: Manages encrypted balances for users in encrypted manner
 *
 * The contract uses three main components:
 * 1. TokenTracker: Manages token registration and tracking
 * 2. EncryptedUserBalances: Handles encrypted balance storage and updates
 * 3. AuditorManager: Manages auditor-related functionality
 */
contract EncryptedERC is TokenTracker, EncryptedUserBalances, AuditorManager {
    ///////////////////////////////////////////////////
    ///                   State Variables           ///
    ///////////////////////////////////////////////////

    /// @notice Address of the registrar contract that manages user registration
    IRegistrar public registrar;

    /// @notice Verifier contracts for each operation
    IMintVerifier public mintVerifier;
    IWithdrawVerifier public withdrawVerifier;
    ITransferVerifier public transferVerifier;
    IBurnVerifier public burnVerifier;

    /// @notice Token metadata
    string public name;
    string public symbol;
    uint8 public immutable decimals;

    /// @notice Mapping to track used mint nullifiers to prevent double-minting
    mapping(uint256 mintNullifier => bool isUsed) public alreadyMinted;

    ///////////////////////////////////////////////////
    ///                    Events                   ///
    ///////////////////////////////////////////////////

    /**
     * @notice Emitted when a private mint operation occurs
     * @param user Address of the user receiving the minted tokens
     * @param auditorPCT Auditor PCT values for compliance tracking
     * @param auditorAddress Address of the auditor
     * @dev This event is emitted when tokens are privately minted to a user
     */
    event PrivateMint(
        address indexed user,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    /**
     * @notice Emitted when a private burn operation occurs
     * @param user Address of the user burning the tokens
     * @param auditorPCT Auditor PCT values for compliance tracking
     * @param auditorAddress Address of the auditor
     * @dev This event is emitted when tokens are privately burned by a user
     */
    event PrivateBurn(
        address indexed user,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    /**
     * @notice Emitted when a private transfer operation occurs
     * @param from Address of the sender
     * @param to Address of the receiver
     * @param auditorPCT Auditor PCT values for compliance tracking
     * @param auditorAddress Address of the auditor
     * @dev This event is emitted when tokens are privately transferred between users
     */
    event PrivateTransfer(
        address indexed from,
        address indexed to,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    /**
     * @notice Emitted when a deposit operation occurs
     * @param user Address of the user making the deposit
     * @param amount Amount of tokens deposited
     * @param dust Amount of dust (remainder) from the deposit
     * @param tokenId ID of the token being deposited
     * @dev This event is emitted when a user deposits tokens into the contract
     */
    event Deposit(
        address indexed user,
        uint256 amount,
        uint256 dust,
        uint256 tokenId
    );

    /**
     * @notice Emitted when a withdrawal operation occurs
     * @param user Address of the user making the withdrawal
     * @param amount Amount of tokens withdrawn
     * @param tokenId ID of the token being withdrawn
     * @param auditorPCT Auditor PCT values for compliance tracking
     * @param auditorAddress Address of the auditor
     * @dev This event is emitted when a user withdraws tokens from the contract
     */
    event Withdraw(
        address indexed user,
        uint256 amount,
        uint256 tokenId,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    ///////////////////////////////////////////////////
    ///                   Modifiers                 ///
    ///////////////////////////////////////////////////
    modifier onlyIfUserRegistered(address user) {
        bool isRegistered = registrar.isUserRegistered(user);
        if (!isRegistered) {
            revert UserNotRegistered();
        }
        _;
    }

    ///////////////////////////////////////////////////
    ///                   Constructor               ///
    ///////////////////////////////////////////////////

    /**
     * @notice Initializes the EncryptedERC contract with the given parameters
     * @param params The initialization parameters containing contract addresses and token metadata
     * @dev This constructor sets up the contract with necessary verifiers, registrar, and token metadata.
     *      It also determines whether the contract will function as a converter or standalone token.
     */
    constructor(
        CreateEncryptedERCParams memory params
    ) TokenTracker(params.isConverter) {
        // Validate contract addresses
        if (
            params.registrar == address(0) ||
            params.mintVerifier == address(0) ||
            params.withdrawVerifier == address(0) ||
            params.transferVerifier == address(0) ||
            params.burnVerifier == address(0)
        ) {
            revert ZeroAddress();
        }

        // Initialize contracts
        registrar = IRegistrar(params.registrar);
        mintVerifier = IMintVerifier(params.mintVerifier);
        withdrawVerifier = IWithdrawVerifier(params.withdrawVerifier);
        transferVerifier = ITransferVerifier(params.transferVerifier);
        burnVerifier = IBurnVerifier(params.burnVerifier);

        // if contract is not a converter, then set the name and symbol
        if (!params.isConverter) {
            name = params.name;
            symbol = params.symbol;
        }

        decimals = params.decimals;
    }

    ///////////////////////////////////////////////////
    ///                   External                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Sets the auditor's public key for a registered user
     * @param user Address of the user to set as auditor
     * @dev This function:
     *      1. Verifies the user is registered
     *      2. Retrieves the user's public key
     *      3. Updates the auditor's information
     *
     * Requirements:
     * - Caller must be the contract owner
     * - User must be registered
     */
    function setAuditorPublicKey(
        address user
    ) external onlyOwner onlyIfUserRegistered(user) {
        uint256[2] memory publicKey_ = registrar.getUserPublicKey(user);
        _updateAuditor(user, publicKey_);
    }

    /**
     * @notice Performs a private mint operation for a registered user
     * @param user The address of the user to mint tokens to
     * @param proof The zero-knowledge proof proving the validity of the mint operation
     * @dev This function:
     *      1. Validates the chain ID and user registration
     *      2. Verifies the user's public key matches the proof
     *      3. Verifies the auditor's public key matches the proof
     *      4. Checks the mint nullifier hasn't been used
     *      5. Verifies the zero-knowledge proof
     *      6. Updates the user's encrypted balance
     *
     * Requirements:
     * - Caller must be the contract owner
     * - Auditor must be set
     * - Contract must be in standalone mode
     * - User must be registered
     * - Proof must be valid
     */
    function privateMint(
        address user,
        MintProof calldata proof
    )
        external
        onlyOwner
        onlyIfAuditorSet
        onlyForStandalone
        onlyIfUserRegistered(user)
    {
        uint256[24] memory publicInputs = proof.publicSignals;

        // Validate chain ID
        if (block.chainid != publicInputs[0]) {
            revert InvalidChainId();
        }

        // validate public keys
        _validatePublicKey(user, [publicInputs[2], publicInputs[3]]);
        _validateAuditorPublicKey([publicInputs[15], publicInputs[16]]);

        // Validate and check mint nullifier
        uint256 mintNullifier = publicInputs[1];
        if (mintNullifier >= BabyJubJub.Q) {
            revert InvalidNullifier();
        }
        if (alreadyMinted[mintNullifier]) {
            revert InvalidProof();
        }

        // Verify the zero-knowledge proof
        bool isVerified = mintVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        {
            // Extract the encrypted amount from the proof
            EGCT memory encryptedAmount = EGCT({
                c1: Point({x: publicInputs[4], y: publicInputs[5]}),
                c2: Point({x: publicInputs[6], y: publicInputs[7]})
            });

            // Extract amount PCT
            uint256[7] memory amountPCT;
            for (uint256 i = 0; i < 7; i++) {
                amountPCT[i] = publicInputs[8 + i];
            }

            // Perform the private mint operation
            _privateMint(user, encryptedAmount, amountPCT);
        }

        // mark the mint nullifier as used
        alreadyMinted[mintNullifier] = true;

        uint256[7] memory auditorPCT;
        for (uint256 i = 0; i < auditorPCT.length; i++) {
            auditorPCT[i] = publicInputs[17 + i];
        }

        emit PrivateMint(user, auditorPCT, auditor);
    }

    /**
     * @notice Performs a private burn operation
     * @param proof The transfer proof proving the validity of the burn operation
     * @param balancePCT The balance PCT for the sender after the burn
     * @dev This function:
     *      1. Validates the sender is registered
     *      2. Verifies the sender's public key matches the proof
     *      3. Verifies the burn address's public key matches the proof
     *      4. Verifies the auditor's public key matches the proof
     *      5. Verifies the zero-knowledge proof
     *      6. Transfers the encrypted amount to the burn address
     *
     * Requirements:
     * - Auditor must be set
     * - Contract must be in standalone mode
     * - Sender must be registered
     * - Proof must be valid
     */
    function privateBurn(
        BurnProof calldata proof,
        uint256[7] calldata balancePCT
    )
        external
        onlyIfAuditorSet
        onlyForStandalone
        onlyIfUserRegistered(msg.sender)
    {
        uint256[19] calldata publicInputs = proof.publicSignals;
        address from = msg.sender;

        // validate public key
        _validatePublicKey(from, [publicInputs[0], publicInputs[1]]);

        // validate auditor public key
        _validateAuditorPublicKey([publicInputs[10], publicInputs[11]]);

        // Verify the zero-knowledge proof
        bool isVerified = burnVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        // provided encrypted balance
        EGCT memory providedBalance = EGCT({
            c1: Point({x: publicInputs[2], y: publicInputs[3]}),
            c2: Point({x: publicInputs[4], y: publicInputs[5]})
        });

        // extract encrypted burn amount
        EGCT memory encryptedBurnAmount = EGCT({
            c1: Point({x: publicInputs[6], y: publicInputs[7]}),
            c2: Point({x: publicInputs[8], y: publicInputs[9]})
        });

        // perform the burn (since burn is only for Standalone, always passing tokenId as 0)
        _privateBurn(from, 0, providedBalance, encryptedBurnAmount, balancePCT);

        // extract auditor PCT
        uint256[7] memory auditorPCT;
        for (uint256 i = 0; i < auditorPCT.length; i++) {
            auditorPCT[i] = publicInputs[12 + i];
        }

        emit PrivateBurn(from, auditorPCT, auditor);
    }

    /**
     * @notice Performs a private transfer between two users
     * @param to Address of the receiver
     * @param tokenId ID of the token to transfer
     * @param proof The transfer proof proving the validity of the transfer
     * @param balancePCT The balance PCT for the sender after the transfer
     * @dev This function:
     *      1. Validates both sender and receiver are registered
     *      2. Verifies both public keys match the proof
     *      3. Verifies the auditor's public key matches the proof
     *      4. Verifies the zero-knowledge proof
     *      5. Updates both users' encrypted balances
     *
     * Requirements:
     * - Auditor must be set
     * - Both sender and receiver must be registered
     * - Proof must be valid
     */
    function transfer(
        address to,
        uint256 tokenId,
        TransferProof memory proof,
        uint256[7] calldata balancePCT
    )
        public
        onlyIfAuditorSet
        onlyIfUserRegistered(msg.sender)
        onlyIfUserRegistered(to)
    {
        uint256[32] memory publicInputs = proof.publicSignals;

        // validate user's public key
        _validatePublicKey(msg.sender, [publicInputs[0], publicInputs[1]]);
        _validatePublicKey(to, [publicInputs[10], publicInputs[11]]);

        _validateAuditorPublicKey([publicInputs[23], publicInputs[24]]);

        // Verify the zero-knowledge proof
        bool isVerified = transferVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        // Extract the inputs for the transfer operation
        TransferInputs memory transferInputs = _extractTransferInputs(
            publicInputs
        );

        // Perform the transfer
        _transfer({
            from: msg.sender,
            to: to,
            tokenId: tokenId,
            providedBalance: transferInputs.providedBalance,
            senderEncryptedAmount: transferInputs.senderEncryptedAmount,
            receiverEncryptedAmount: transferInputs.receiverEncryptedAmount,
            balancePCT: balancePCT,
            amountPCT: transferInputs.amountPCT
        });

        // Extract auditor PCT and emit event
        {
            uint256[7] memory auditorPCT;
            for (uint256 i = 0; i < 7; i++) {
                auditorPCT[i] = publicInputs[25 + i];
            }

            emit PrivateTransfer(msg.sender, to, auditorPCT, auditor);
        }
    }

    /**
     * @notice Deposits an existing ERC20 token into the contract
     * @param amount Amount of tokens to deposit
     * @param tokenAddress Address of the token to deposit
     * @param amountPCT Amount PCT for the deposit
     * @dev This function:
     *      1. Validates the user is registered
     *      2. Transfers the tokens from the user to the contract
     *      3. Converts the tokens to encrypted tokens
     *      4. Adds the encrypted amount to the user's balance
     *      5. Returns any dust (remainder) to the user
     *
     * Requirements:
     * - Auditor must be set
     * - Contract must be in converter mode
     * - Token must not be blacklisted
     * - User must be registered
     */
    function deposit(
        uint256 amount,
        address tokenAddress,
        uint256[7] memory amountPCT
    )
        public
        onlyIfAuditorSet
        onlyForConverter
        revertIfBlacklisted(tokenAddress)
        onlyIfUserRegistered(msg.sender)
    {
        IERC20 token = IERC20(tokenAddress);
        uint256 dust;
        uint256 tokenId;
        address to = msg.sender;

        // Get the contract's balance before the transfer
        uint256 balanceBefore = token.balanceOf(address(this));

        // Transfer tokens from user to contract
        SafeERC20.safeTransferFrom(token, to, address(this), amount);

        // Get the contract's balance after the transfer
        uint256 balanceAfter = token.balanceOf(address(this));

        // Verify that the actual transferred amount matches the expected amount
        uint256 actualTransferred = balanceAfter - balanceBefore;
        if (actualTransferred != amount) {
            revert TransferFailed();
        }

        // Convert tokens to encrypted tokens
        (dust, tokenId) = _convertFrom(to, amount, tokenAddress, amountPCT);

        // Return dust to user
        SafeERC20.safeTransfer(token, to, dust);

        // Emit deposit event
        emit Deposit(to, amount, dust, tokenId);
    }

    /**
     * @notice Withdraws encrypted tokens as regular ERC20 tokens
     * @param tokenId ID of the token to withdraw
     * @param proof The withdraw proof proving the validity of the withdrawal
     * @param balancePCT The balance PCT for the user after the withdrawal
     * @dev This function:
     *      1. Validates the user is registered
     *      2. Verifies the user's public key matches the proof
     *      3. Verifies the auditor's public key matches the proof
     *      4. Verifies the zero-knowledge proof
     *      5. Subtracts the encrypted amount from the user's balance
     *      6. Converts the tokens to regular ERC20 tokens
     *
     * Requirements:
     * - Auditor must be set
     * - Contract must be in converter mode
     * - User must be registered
     * - Proof must be valid
     */
    function withdraw(
        uint256 tokenId,
        WithdrawProof memory proof,
        uint256[7] memory balancePCT
    )
        public
        onlyIfAuditorSet
        onlyForConverter
        onlyIfUserRegistered(msg.sender)
    {
        address from = msg.sender;
        uint256[16] memory publicInputs = proof.publicSignals;
        uint256 amount = publicInputs[0];

        // validate public keys
        _validatePublicKey(from, [publicInputs[1], publicInputs[2]]);
        _validateAuditorPublicKey([publicInputs[7], publicInputs[8]]);

        // Verify the zero-knowledge proof
        bool isVerified = withdrawVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        // Perform the withdrawal
        _withdraw(from, amount, tokenId, publicInputs, balancePCT);

        // Extract auditor PCT and emit event
        {
            uint256[7] memory auditorPCT;
            for (uint256 i = 0; i < 7; i++) {
                auditorPCT[i] = publicInputs[9 + i];
            }

            emit Withdraw(from, amount, tokenId, auditorPCT, auditor);
        }
    }

    /**
     * @notice Gets the encrypted balance for a token address
     * @param user Address of the user
     * @param tokenAddress Address of the token
     * @return eGCT The ElGamal ciphertext representing the encrypted balance
     * @return nonce The current nonce used for balance validation
     * @return amountPCTs Array of amount PCTs for transaction history
     * @return balancePCT The current balance PCT
     * @return transactionIndex The current transaction index
     * @dev This is a convenience function that looks up the token ID and calls balanceOf
     */
    function getBalanceFromTokenAddress(
        address user,
        address tokenAddress
    )
        public
        view
        returns (
            EGCT memory eGCT,
            uint256 nonce,
            AmountPCT[] memory amountPCTs,
            uint256[7] memory balancePCT,
            uint256 transactionIndex
        )
    {
        uint256 tokenId = tokenIds[tokenAddress];
        return balanceOf(user, tokenId);
    }

    ///////////////////////////////////////////////////
    ///                   Internal                  ///
    ///////////////////////////////////////////////////

    /**
     * @notice Performs the internal logic for a private withdrawal
     * @param from Address of the user withdrawing tokens
     * @param amount Amount of tokens to withdraw
     * @param tokenId ID of the token to withdraw
     * @param publicInputs Public inputs from the proof
     * @param balancePCT The balance PCT for the user after the withdrawal
     * @dev This function:
     *      1. Validates the token exists
     *      2. Verifies the provided balance is valid
     *      3. Subtracts the encrypted amount from the user's balance
     *      4. Converts the tokens to regular ERC20 tokens
     */
    function _withdraw(
        address from,
        uint256 amount,
        uint256 tokenId,
        uint256[16] memory publicInputs,
        uint256[7] memory balancePCT
    ) internal {
        address tokenAddress = tokenAddresses[tokenId];
        if (tokenAddress == address(0)) {
            revert UnknownToken();
        }

        {
            // Extract the provided balance from the proof
            EGCT memory providedBalance = EGCT({
                c1: Point({x: publicInputs[3], y: publicInputs[4]}),
                c2: Point({x: publicInputs[5], y: publicInputs[6]})
            });

            // Encrypt the withdrawn amount
            EGCT memory encryptedWithdrawnAmount = BabyJubJub.encrypt(
                Point({x: publicInputs[1], y: publicInputs[2]}),
                amount
            );

            _privateBurn(
                from,
                tokenId,
                providedBalance,
                encryptedWithdrawnAmount,
                balancePCT
            );
        }

        // Convert and transfer the tokens
        _convertTo(from, amount, tokenAddress);
    }

    /**
     * @notice Converts regular ERC20 tokens to encrypted tokens
     * @param to Address of the receiver
     * @param amount Amount of tokens to convert
     * @param tokenAddress Address of the token to convert
     * @param amountPCT Amount PCT for the conversion
     * @return dust The dust (remainder) from the conversion
     * @return tokenId The ID of the token
     * @dev This function:
     *      1. Handles decimal scaling between tokens
     *      2. Registers the token if it's new
     *      3. Encrypts the amount with the receiver's public key
     *      4. Adds the encrypted amount to the receiver's balance
     */
    function _convertFrom(
        address to,
        uint256 amount,
        address tokenAddress,
        uint256[7] memory amountPCT
    ) internal returns (uint256 dust, uint256 tokenId) {
        // Get token decimals and handle scaling
        uint8 tokenDecimals = IERC20Metadata(tokenAddress).decimals();

        uint256 value = amount;
        dust = 0;

        // Scale down if token has more decimals
        if (tokenDecimals > decimals) {
            uint256 scalingFactor = 10 ** (tokenDecimals - decimals);
            value = amount / scalingFactor;
            dust = amount % scalingFactor;
        }
        // Scale up if token has fewer decimals
        else if (tokenDecimals < decimals) {
            uint256 scalingFactor = 10 ** (decimals - tokenDecimals);
            value = amount * scalingFactor;
            dust = 0;
        }

        // Register the token if it's new
        if (tokenIds[tokenAddress] == 0) {
            _addToken(tokenAddress);
        }
        tokenId = tokenIds[tokenAddress];

        // Return early if the scaled value is zero
        if (value == 0) {
            return (dust, tokenId);
        }

        // Encrypt and add to balance
        {
            // Get the receiver's public key
            uint256[2] memory publicKey = registrar.getUserPublicKey(to);

            // Encrypt the value with the receiver's public key
            EGCT memory eGCT = BabyJubJub.encrypt(
                Point({x: publicKey[0], y: publicKey[1]}),
                value
            );

            // Add to the receiver's balance
            EncryptedBalance storage balance = balances[to][tokenId];

            if (balance.eGCT.c1.x == 0 && balance.eGCT.c1.y == 0) {
                balance.eGCT = eGCT;
            } else {
                balance.eGCT.c1 = BabyJubJub._add(balance.eGCT.c1, eGCT.c1);
                balance.eGCT.c2 = BabyJubJub._add(balance.eGCT.c2, eGCT.c2);
            }

            // Update transaction history
            balance.amountPCTs.push(
                AmountPCT({pct: amountPCT, index: balance.transactionIndex})
            );
            balance.transactionIndex++;

            // Commit the new balance
            _commitUserBalance(to, tokenId);
        }

        return (dust, tokenId);
    }

    /**
     * @notice Converts encrypted tokens to regular ERC20 tokens
     * @param to Address of the receiver
     * @param amount Amount of tokens to convert
     * @param tokenAddress Address of the token to convert to
     * @dev This function:
     *      1. Handles decimal scaling between tokens
     *      2. Transfers the tokens to the receiver
     */
    function _convertTo(
        address to,
        uint256 amount,
        address tokenAddress
    ) internal {
        // Get token decimals and handle scaling
        uint256 tokenDecimals = IERC20Metadata(tokenAddress).decimals();

        uint256 value = amount;
        uint256 scalingFactor = 0;

        // Scale up if token has more decimals
        if (tokenDecimals > decimals) {
            scalingFactor = 10 ** (tokenDecimals - decimals);
            value = amount * scalingFactor;
        }
        // Scale down if token has fewer decimals
        else if (tokenDecimals < decimals) {
            scalingFactor = 10 ** (decimals - tokenDecimals);
            value = amount / scalingFactor;
        }

        // Transfer the tokens to the receiver
        IERC20 token = IERC20(tokenAddress);
        SafeERC20.safeTransfer(token, to, value);
    }

    /**
     * @notice Performs the internal logic for a private mint
     * @param user Address of the user to mint tokens to
     * @param encryptedAmount The encrypted amount to mint
     * @param amountPCT The amount PCT for the mint
     * @dev This function:
     *      1. Adds the encrypted amount to the user's balance
     *      2. Emits a PrivateMint event
     */
    function _privateMint(
        address user,
        EGCT memory encryptedAmount,
        uint256[7] memory amountPCT
    ) internal {
        // since private mint is only for the standalone ERC, tokenId is always 0
        _addToUserBalance(user, 0, encryptedAmount, amountPCT);
    }

    /**
     * @notice Performs the internal logic for a private transfer
     * @param from address The address of the sender
     * @param to address The address of the receiver
     * @param tokenId uint256 The ID of the token to transfer
     * @param providedBalance EGCT The provided balance from the proof
     * @param senderEncryptedAmount EGCT The encrypted amount to subtract from the sender's balance
     * @param receiverEncryptedAmount EGCT The encrypted amount to add to the receiver's balance
     * @param balancePCT uint256[7] The balance PCT for the sender after the transfer
     * @param amountPCT uint256[7] The amount PCT for the transfer
     * @dev This function:
     *      1. Verifies the sender's balance is valid
     *      2. Subtracts the encrypted amount from the sender's balance
     *      3. Adds the encrypted amount to the receiver's balance
     */
    function _transfer(
        address from,
        address to,
        uint256 tokenId,
        EGCT memory providedBalance,
        EGCT memory senderEncryptedAmount,
        EGCT memory receiverEncryptedAmount,
        uint256[7] memory balancePCT,
        uint256[7] memory amountPCT
    ) internal {
        {
            // 1. for sender operation is very similar to the private burn
            _privateBurn(
                from,
                tokenId,
                providedBalance,
                senderEncryptedAmount,
                balancePCT
            );
        }

        {
            // 2. for receiver operation is very similar to the private mint
            _addToUserBalance(to, tokenId, receiverEncryptedAmount, amountPCT);
        }
    }

    /**
     * @notice Performs the internal logic for a private burn
     * @param from Address of the user to burn tokens from
     * @param tokenId ID of the token to burn
     * @param providedBalance The provided balance from the proof
     * @param encryptedAmount The encrypted amount to subtract
     * @param balancePCT The balance PCT for the user after the burn
     * @dev This function:
     *      1. Verifies the user's balance is valid
     *      2. Subtracts the encrypted amount from the user's balance
     */
    function _privateBurn(
        address from,
        uint256 tokenId,
        EGCT memory providedBalance,
        EGCT memory encryptedAmount,
        uint256[7] memory balancePCT
    ) internal {
        // verify user encrypted balance
        uint256 transactionIndex = _verifyUserBalance(
            from,
            tokenId,
            providedBalance
        );

        // subtract from user's balance
        _subtractFromUserBalance(
            from,
            tokenId,
            encryptedAmount,
            balancePCT,
            transactionIndex
        );
    }

    /**
     * @notice Validates a user's public key
     * @param user The address of the user
     * @param providedPublicKey The public key to validate
     * @dev Function fetches the user's public key from the registrar contract
     * @dev If the public key is not valid, it reverts with InvalidProof error
     */
    function _validatePublicKey(
        address user,
        uint256[2] memory providedPublicKey
    ) internal view {
        uint256[2] memory userPublicKey = registrar.getUserPublicKey(user);

        if (
            userPublicKey[0] != providedPublicKey[0] ||
            userPublicKey[1] != providedPublicKey[1]
        ) {
            revert InvalidProof();
        }
    }

    /**
     * @notice Validates the auditor's public key
     * @param providedPublicKey The public key to validate
     * @dev If the public key is not match with the auditor's public key, it reverts with InvalidProof error
     */
    function _validateAuditorPublicKey(
        uint256[2] memory providedPublicKey
    ) internal view {
        if (
            auditorPublicKey.x != providedPublicKey[0] ||
            auditorPublicKey.y != providedPublicKey[1]
        ) {
            revert InvalidProof();
        }
    }

    /**
     * @notice Extracts the inputs for a transfer operation
     * @param input The input array containing the transfer data
     * @return transferInputs TransferInputs struct containing:
     *         - providedBalance (EGCT): The provided balance from the proof
     *         - senderEncryptedAmount (EGCT): The encrypted amount to subtract from sender
     *         - receiverEncryptedAmount (EGCT): The encrypted amount to add to receiver
     *         - amountPCT (uint256[7]): The amount PCT for the transfer
     */
    function _extractTransferInputs(
        uint256[32] memory input
    ) internal pure returns (TransferInputs memory transferInputs) {
        transferInputs.providedBalance = EGCT({
            c1: Point({x: input[2], y: input[3]}),
            c2: Point({x: input[4], y: input[5]})
        });

        transferInputs.senderEncryptedAmount = EGCT({
            c1: Point({x: input[6], y: input[7]}),
            c2: Point({x: input[8], y: input[9]})
        });

        transferInputs.receiverEncryptedAmount = EGCT({
            c1: Point({x: input[12], y: input[13]}),
            c2: Point({x: input[14], y: input[15]})
        });

        for (uint256 i = 0; i < 7; i++) {
            transferInputs.amountPCT[i] = input[16 + i];
        }
    }
}

// src/Token.sol

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

// src/TokenLaunchereERC20.sol

 // Assuming this is where MyEncryptedToken is defined

contract TokenLauncher {
    // Struct for token details
    struct TokenDetails {
        string name;
        string symbol;
        uint8 decimals;
        address tokenAddress;
    }

    // Mapping to store token details by name
    mapping(string => TokenDetails) public tokenDetailsMap;

    // Counter for number of tokens created
    uint256 public tokenCount;

    // Mapping to store token names by index (replaces array)
    mapping(uint256 => string) public tokenNamesByIndex;

    // Event emitted when a token is created
    event TokenCreated(address indexed tokenAddress, string name, string symbol, uint8 decimals);

    // Function to launch a new token
    function launchToken(
        string memory name,
        string memory symbol,
        uint8 decimals,
        address registrar,
        address allPurposeVerifier
    ) external returns (address) {
        // Deploy new MyEncryptedToken
        MyEncryptedToken newToken = new MyEncryptedToken(
            name,
            symbol,
            decimals,
            registrar,
            allPurposeVerifier
        );

        // Store token details in mapping
        tokenDetailsMap[name] = TokenDetails(
            name,
            symbol,
            decimals,
            address(newToken)
        );

        // Store name by index and increment counter
        tokenNamesByIndex[tokenCount] = name;
        tokenCount++;

        // Emit event
        emit TokenCreated(address(newToken), name, symbol, decimals);

        return address(newToken);
    }

    // Function to get details of a specific token by name
    function getTokenDetails(string memory _name) external view returns (string memory, string memory, uint8, address) {
        TokenDetails memory details = tokenDetailsMap[_name];
        return (details.name, details.symbol, details.decimals, details.tokenAddress);
    }

    // Function to get all token details without relying on an array
    function getAllTokenDetails() external view returns (TokenDetails[] memory) {
        TokenDetails[] memory allDetails = new TokenDetails[](tokenCount);
        for (uint256 i = 0; i < tokenCount; i++) {
            string memory name = tokenNamesByIndex[i];
            allDetails[i] = tokenDetailsMap[name];
        }
        return allDetails;
    }
}

