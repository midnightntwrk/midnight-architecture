# %% [markdown]
# # Overview
# This is a library to support simulated contracts on the Cardano network.  Its purpose is to allow behavioral specifications of desired contract behaviors in a commonly understood language (Python) while still leaving it up to Cardano developers to design and implement actual Plutus contracts to realize these behaviors on Cardano.
# %% [markdown]
# ## Standard Imports and Utilities
# %%
import os
from dataclasses import dataclass
from enum import Enum
from datetime import datetime, timedelta
from copy import copy, deepcopy

DEBUG = False
def debug(s):
  if DEBUG:
    print(s)
debug('debugging enabled')

# %% [markdown]
# # Cryptography and Wallets
# 
# It's not practical to model a blockchain without some realy cryptography.  We import some standard libs, define some utilities, and then define a wallet based on these primitives.
# %%
# https://cryptography.io/en/latest/
from cryptography.hazmat.primitives.asymmetric.types import PublicKeyTypes
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPublicKey
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat, load_ssh_public_key
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import rsa, padding
from cryptography.exceptions import InvalidSignature

class PublicKey():
  def __init__(self, binary_pk: RSAPublicKey) -> None:
    self.binary_pk = binary_pk
    self.repr = PublicKey._make_repr(self.binary_pk)
  def ser(self):
    return self.binary_pk.public_bytes(encoding=Encoding.OpenSSH, format=PublicFormat.OpenSSH)
  @classmethod
  def des(cls, pk_string):
    return PublicKey(load_ssh_public_key(pk_string))
  @classmethod
  def _make_repr(cls, binary_pk):
    repr = binary_pk.public_bytes(encoding=Encoding.OpenSSH, format=PublicFormat.OpenSSH)[60:68]
    return f'pk:{repr!r}'
  def verify(self, sig: bytes, data: bytes):
      try:
        self.binary_pk.verify(
          sig,
          data,
          padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
          hashes.SHA256())
        return True
      except InvalidSignature:
        return False
  def __getstate__(self) -> object:
    return self.ser()
  def __setstate__(self, pk_string):
    self.binary_pk = load_ssh_public_key(pk_string)
    self.repr = PublicKey._make_repr(self.binary_pk)
  def __repr__(self) -> str:
    return self.repr  

@dataclass
class SignedMessage:
  signature: bytes
  message: bytes

# %%
def dumbhash(obj):
  return bytearray(obj, 'utf-8')

# %%
class InsufficientFunds(Exception):
  pass
class ValidationException(Exception):
  pass

def ensure(b: bool, msg: str):
  if not b:
    raise ValidationException(msg)

# %%
class CNA(Enum):
  XLOV = 0  # fractional XADA
  ZTAR = 1  # fractional ZIGHT

# A user-visible utility for describing an amount of some token type.
@dataclass
class TokenValue:
  cna: CNA
  num: int

def tv_as_bag(self: TokenValue):
  return dict({self.cna : self.num})
TokenValue.as_bag = tv_as_bag

def add_tokens(bag: dict, cna: CNA, num: int):
  if num != 0:
    bag[cna] = bag.get(cna, 0) + num

def sum_toks(caller, utxos):
  debug(f'{caller} utxos to sum {utxos}')
  sum = dict()
  for x in utxos:
    debug(f'utxo to sum {x}')
    for cna in x.toks():
      add_tokens(sum, cna, x.toks()[cna])
  return sum


# %%
class Wallet:
  def __init__(self, ledger) -> None:
    self.ledger = ledger
    self.sk = rsa.generate_private_key(
      public_exponent=65537,
      key_size=2048)
    self.pk = PublicKey(self.sk.public_key())
  def sign(self, message : bytes):
    return self.sk.sign(
      message,
      padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
      hashes.SHA256())
  def make_signed_message(self, message : bytes):
    sig = self.sign(message);
    return SignedMessage(sig, message)
  def balance(self):
    b = dict()
    if self.pk in self.ledger.plain_utxos_by_pk:
      for x in self.ledger.plain_utxos_by_pk[self.pk]:
        for cna in x.toks():
          add_tokens(b, cna, x.toks()[cna])
    return b
  def select_coins(self, needed):
    """
    Naive coin selection, choosing arbitrary utxos with the needed tokens.

    Args:
        needed: a map {cna: num, ...} of needed tokens

    Returns:
        A tuple (inputs, remainders) where inputs is a list of utxo hashes
        and remainders is a map {cna: num, ...} of excess tokens from
        the given inputs beyond what was `needed`.

    Raises:
        InsufficientFunds if there are not enough tokens to satisfy the need
    """
    needed = copy(needed)
    inputs = list()
    remainders = dict()
    if self.pk not in self.ledger.plain_utxos_by_pk:
      raise InsufficientFunds(repr(needed))
    for x in self.ledger.plain_utxos_by_pk[self.pk]:
      if len(needed.keys()) == 0:
        break
      common_cnas = [cna for cna in x.toks() if cna in needed]
      # if there is any intersection, we will use the utxo
      if len(common_cnas) > 0:
        inputs.append(x.hash)
        # any non-intersecting cna types belong in remainders
        for unwanted in [cna for cna in x.toks() if cna not in needed]:
          add_tokens(remainders, cna, unwanted[cna])
        # any intersecting cna types are used, but may also have remainders
        for cna in common_cnas:
          needed[cna] = needed[cna] - x.toks()[cna]
          if needed[cna] <= 0:
            # add any excess to remainders
            add_tokens(remainders, cna, -1 * needed[cna])
            # need satisfied
            del needed[cna]
    if len(needed.keys()) > 0:
      raise InsufficientFunds(repr(needed))
    return (inputs, remainders)

# %% [markdown]
# # Simplifying Assumptions
# 
# The smart contract model we simulate is deliberately simplified from the general EUTXO model supported by Plutus, but should be sufficient for basic modeling of many smart contracts for overall logic and token flows.  Our model works as follows:
# 
# * Every utxo is either:
#   * Plain (a bag of tokens of multiple types) protected by a pk
#   * A contract, which can also hold a bag of tokens.
# * Every tx is one of:
#   * A spend
#   * A deploy (contract)
#   * A contract call
# * Every tx has a tx hash computed from its inputs and outputs
# * Every input utxo is distinct
# * Every tx includes a signature for the tx hash
# * Every tx has both input and output utxos
#   * Each input utxo is just the hash of an on-chain plain utxo
#   * Each output utxo can be either a plain or contract utxo object.
#   * Contract calls additionally include the hash of the single contract utxo that is being called.
# 
# Since both utxo types include a bag of tokens, we define an abastract base class `Utxo` that includes this bag, which we model as a dictionary mapping token types to token counts.
# 
# Plain utxos are modeled with a concrete `PlainUtxo` class that extends `Utxo` with a `pk` field.
# 
# Contract utxos are modeled with a concrete `ContractUtxo` class that extends `Utxo` with a contract instance that implments a `call` method that takes the following parameters:
# 
# * ctx: the evaluation context (of type `ContractContext`)
# * method_name: which method is being invoked
# * my_toks: the contract's own token dict
# * args: user-supplied arguments, which may include tokens gathered from the input utxos.
# 
# 
# ## General Tx Validity
# 
# Each tx type has its own validity conditions, but they all obey the following validity requirements:
# 
# * Each input utxo hash resolved to an active utxo object in the ledger
# * The input utxos are all locked by the same pk
# * This shared locking pk successfully verifies the tx signature
# * The sum (per token type) of tokens across all input utxos $\geq$ the sum of all output utxos plus a nominal tx fee (a simulation parameter).  
# 
# Moreover, any excess tokens are considered burned since there is no block producer in our model to reward.
# 
# ## Spend Transactions
# 
# A spend tx has plain utxos as its inputs and outputs.
# 
# The tx is valid if the general validity check succeeds.
# 
# The result of a successful spend is that:
# 
# * Every input utxo is set to a deleted state and is removed from the ledger.
# * Every output utxo is added to the ledger and indexed by the pk that locks it (as specified in the PlainUtxo object)
# 
# ## Deploy Transactions
# 
# A deploy tx has plain utxos as its inputs and one or more contract utxo among its outputs.  The tx inlcues:
# 
# * The uninitialized contract
# * An argument list to initialized the contract
# 
# The contract utxo has the following fields:
# 
# * The contract object with user-defined methods
# * A bag of tokens (of multiple types) held by the contract
# 
# A tx is valid if all of the following hold:
# 
# * The general validity check succeeds
# * The inputs cover a standard deployment fee (a simulation parameter) per deployed contract.
# * The tokens in the contract utxo's `toks` bag include at least one XADA (the "min XADA" deposit).
# 
# The ledger initializes the contract state by calling an initialization method on the contract that takes user-specied arguments.
# 
# The argument list to the initialization method can include special arguments that make input tokens available to the contract.  Each token-input argument is an instance of `TokenValue` that specifies:
# * The token type
# * The number of tokens
# 
# The return value of a successful deploy transaction is the `utxo_id` of the deployed contract.  Unlike Plutus, this will be the contract's address for its whole deployment.
# 
# ## Call Transactions
# 
# Each call tx includes:
# 
# * A designated callee, represented as the hash of a contract utxo
# * Any number of plain input utxos (as hashes)
# * Any number of plain output utxos
# * A call record including:
#   * The contract method name to invoke
#   * A list of arguments to the method
# 
# The argument list to the method can include special arguments that make input tokens available to the contract.  Each token-input argument is an instance of `TokenValue` that specifies:
# * The token type
# * The number of tokens
# 
# Verification of a call tx is split into phases:
# 1. validate the (plain) input utxos by signature
# 2. Invoke the contract method with the given arguments.  
#   * If it succeeds, it returns:
#     * A new contract instance that replaces the prior contract instance in the contract utxo by side effect.  (I.e., the old contract utxo is not consumed as it would be in Cardano.)
#     * A list of (additional) output utxos that are added to the tx's list of output utxos
#   * If it raises an exception, the tx fails without any modification to the contract state and without generating outputs.
# 3. Verify the sum (per token type) of tokens across all input utxos $\geq$ the sum of all output utxos plus a nominal contract tx fee (a simulation parameter).
# 
# Contracts that terminate successfully can return arbitrary Python objects (but it would be nonsensical for them to return, for example, their evaluation context object.
# 
# # Contract External Side Effects
# 
# Every contract method takes an extra argument that is an instance of a `CallContext` object.  This object has methods to support querying and updating some of the ledger state.  This object can answer queries directly.  For side effects such as emitting new UTXOs or deploying/calling contracts, it facilitates the work and ensures that any resulting outputs are transactional and accounted among the tx outputs.
# 
# ## Querying the Ledger
# 
# * `dttm` - the virtual time of the start of execution
# * `toks` - the contract's token dictionary (which it may side effect)
# 
# ## Contracts Emitting UTXOs
# 
# `emit`
# 
# ## Contracts Deploying Contracts
# 
# `deploy`
# 
# ## Contracts Calling Contracts
# 
# `call`
# 
# Every callee contract must be included as an input utxo in the call transaction.
# 
# ### Recursion and reentrance
# 
# Recursion and reentrance are forbidden, and prevented by maintenance of a call trace during contract execution.
# 
# 
# ## Explicit Deviations from Cardano
# 
# A summary of the key devitions of our model from Cardano follows.
# 
# * Contracts are modified in place when successful
# * A tx can invoke only one contract at at time.
# * A contract's state must be concentrated in a single contract utxo.
# * Contract fees are flat
# * Failed contract calls have zero cost
# * Plain utxos all use a simple pk locking script
# * Tx signing unsalfely ignores dynamic contract outputs
# * Utxos are not indexed by tx and index
# * Deploy and call transactions have Python return values
# 
# 
# 
# 

# %% [markdown]
# # Implementation

# %%
class AbstractUtxo:
  def __init__(self) -> None:
    # sometimes a hash is not a hash, it's a random ID
    self.hash = os.urandom(32).hex()
    debug(f'AbstractUtxo {self.hash!r}')

class PlainUtxo(AbstractUtxo):
  def __init__(self, pk: PublicKey, toks: dict):
    super().__init__()
    self.pk = pk
    self._toks = toks
  def toks(self):
    return self._toks
  def __repr__(self) -> str:
    return f'PlainUtxo({self.pk}, {self.toks()})'

# Because we use mutable contracts (in the hope that most readers will
# find them more readable), we need a rollback mechanism for changes.
# We implement this with an envelope/letter pattern where the UTXO
# is the envelope and has a current and pending state (the letter)
# represented as a ContractInst

class ContractInst():
  def __init__(self, contract: object, toks: dict) -> None:
    self.contract = contract
    self.toks = toks
    assert type(contract) != dict
    assert type(toks) == dict

class ContractUtxo(AbstractUtxo):
  def __init__(self, contract: object, toks: dict):
    super().__init__()
    self.letter = ContractInst(contract, toks)
    self.rollback = None
  def toks(self):
    return self.letter.toks
  def contract(self):
    return self.letter.contract
  def tx_prepare(self):
    ensure(not self.rollback, 'cannot prepare_rollback with existing rollback')
    self.rollback = self.letter
    self.letter = deepcopy(self.letter)
    debug("HERE-------------------------------------------------------------")
  def tx_commit(self):
    self.rollback = None
  def tx_preimage(self):
    """
    Return a temporary UTXO for use in validate_outputs.  This UTXO
    represents the current UTXO before transaction verificaiton.
    """
    return ContractUtxo(self.rollback.contract, self.rollback.toks)
  def tx_rollback(self):
    self.letter = self.rollback
    self.rollback = None
  def set_toks_deprecated(self, toks):
    assert type(toks) == dict
    self.letter.toks = toks
  def set_contract_deprecated(self, contract):
    assert type(contract) != dict
    self.letter.contract = contract
  def __repr__(self) -> str:
    return f'ContractUtxo({self.letter.contract.__class__.__name__}, {self.letter.toks})'

# %%
ONE_XADA = 1000000
ONE_ZIGHT = 1000000

MIN_XADA      = ONE_XADA
BASE_TX_FEE   = ONE_XADA
DEPLOY_TX_FEE = 100 * BASE_TX_FEE
CALL_TX_FEE   = 10 * BASE_TX_FEE

def xadas(n):
  return TokenValue(CNA.XLOV, n * ONE_XADA)
def zights(n):
  return TokenValue(CNA.ZTAR, n * ONE_ZIGHT)

# %%
from abc import abstractmethod
class AbstractTx:
  def __init__(self, inputs: list, outputs: list) -> None:
    self.inputs = set(inputs)
    self.outputs = set(outputs)
    debug(f'self.outputs {self.outputs}')
    self.tx_hash = dumbhash(repr((inputs, outputs)))
    self.signature = None # filled by signing
    self.input_utxos = None # filled during verification
    self.sum_inputs = None # filled during verification
  def sign(self, sig: bytes):
    self.signature = sig
  @abstractmethod
  def validate(self, ledger, dttm):
    pass
  def validate_inputs(self, ledger, extra_inputs):
    debug(f'extra_inputs {extra_inputs}')
    ensure(self.signature, "tx must be signed")
    ensure(len(self.inputs) > 0, "tx must have at least one input utxo")
    self.input_utxos = []
    debug(f'self.inputs {self.inputs}')
    for h in self.inputs:
      utxo = ledger.utxos_by_hash[h]
      ensure(utxo, f'utxo not found for hash {h}')
      ensure(type(utxo) == PlainUtxo, "input utxos must be plain")
      self.input_utxos.append(utxo)
    pk = self.input_utxos[0].pk
    for utxo in self.input_utxos:
      ensure(utxo.pk == pk, 'input utxos must be owned by the same key')
    ensure(pk.verify(self.signature, self.tx_hash),
           'input utxos must be owned by the tx signer')
    self.sum_inputs = sum_toks('IN', self.input_utxos + extra_inputs)
    # remove all spent inputs (but not extra inputs)
    for utxo in self.input_utxos:
      ledger.remove_utxo(utxo)
  def validate_outputs(self, ledger, fee, extra_outputs):
    debug(f'validate_outputs(self, ledger, {fee}, {extra_outputs})')
    debug(f'extra_outputs {extra_outputs}')
    ensure(self.input_utxos, 'validate_outputs only after validate_inputs')
    outputs = self.outputs.union(set(extra_outputs))
    debug(f'union {outputs}')
    sum_outputs = sum_toks('OUT', outputs)
    debug(f'summed {sum_outputs}')
    if CNA.XLOV not in sum_outputs: sum_outputs[CNA.XLOV] = 0
    sum_outputs[CNA.XLOV] += fee
    debug(f'sum_inputs {self.sum_inputs}')
    debug(f'sum_outputs {sum_outputs}')
    for cna in sum_outputs:
      ensure(cna in self.sum_inputs
             and self.sum_inputs[cna] >= sum_outputs[cna],
             f'insufficient tokens of type {cna}, {self.sum_inputs[cna]} < {sum_outputs[cna]}')
    # add just self.outputs; if extra_outputs neeed, adding, the caller does it
    for utxo in self.outputs:
      ledger.add_utxo(utxo)

# %%
class SpendTx(AbstractTx):
  def __init__(self, inputs: list, outputs: list) -> None:
    super().__init__(inputs, outputs)
  def validate(self, ledger, dttm):
    self.validate_inputs(ledger, [])
    self.validate_outputs(ledger, BASE_TX_FEE, [])
    return None

def wallet_send(self: Wallet, recipients: dict):
  """
  Create and submit a spend transaction.

  Args:
      recipients: {pk : {cna: num, ...}, ...}
  Return:
      The ledger's response to validating the tx.
  Raises:
      InsufficientFunds if there are not enough tokens to satisfy the need
  """
  # compute the total output tokens
  needed = dict()
  add_tokens(needed, CNA.XLOV, BASE_TX_FEE)
  for pk in recipients:
    for cna in recipients[pk]:
      add_tokens(needed, cna, recipients[pk][cna])
  (inputs, remainders) = self.select_coins(needed)
  # outputs include one for all our remainders, and one for each recipient
  outputs = [PlainUtxo(self.pk, remainders)]
  for pk in recipients:
    outputs.append(PlainUtxo(pk, recipients[pk]))
  # create and sign the transaction
  tx = SpendTx(inputs, outputs)
  tx.sign(self.sign(tx.tx_hash))
  # submit the transaction
  return self.ledger.validate(tx)

# Add method to wallet
Wallet.send = wallet_send

# %%
# For simplicity, we assume the contract is initialized prior to
# the creation of the deploy tx, requiring no on-chain execution.
class DeployTx(AbstractTx):
  def __init__(self,
               inputs  : list,
               outputs : list,
               contract: object,
               toks    : dict,
               ) -> None:
    super().__init__(inputs, outputs)
    self.toks = toks
    self.contract = contract
  def validate(self, ledger, dttm):
    self.validate_inputs(ledger, [])
    ensure(CNA.XLOV in self.toks and self.toks[CNA.XLOV] >= MIN_XADA,
           'deploy missing MIN_XADA')
    contract_utxo = ContractUtxo(self.contract, self.toks)
    self.validate_outputs(ledger, DEPLOY_TX_FEE, [contract_utxo])
    ledger.add_utxo(contract_utxo)
    return contract_utxo.hash

def wallet_deploy(self: Wallet, contract, toks):
  debug(f'deploy {type(contract)} with toks {toks}')
  needed = copy(toks)
  add_tokens(needed, CNA.XLOV, DEPLOY_TX_FEE)
  debug(f'needed = {needed}')
  (inputs, remainders) = self.select_coins(needed)
  outputs = [PlainUtxo(self.pk, remainders)]
  # create and sign the transaction
  tx = DeployTx(inputs, outputs, contract, toks)
  tx.sign(self.sign(tx.tx_hash))
  # submit the transaction
  return self.ledger.validate(tx)

# Add method to wallet
Wallet.deploy = wallet_deploy

# %%
#string_types = (str, unicode) if str is bytes else (str, bytes)
#iteritems = lambda mapping: getattr(mapping, 'iteritems', mapping.items)()

#def _harvest_toks(obj):
#    if isinstance(obj, Mapping):
#        iterator = iteritems
#    elif isinstance(obj, (Sequence, Set)) and not isinstance(obj, string_types):
#        iterator = enumerate
#    if iterator:
#        if id(obj) not in memo:
#           memo.add(id(obj))
#            for path_component, value in iterator(obj):
#                for result in objwalk(value, path + (path_component,), memo):
#                    yield result
#            memo.remove(id(obj))
#    else:
#        yield path, obj

# %%
def harvest_toks(args, kwargs):
  """
  Scan contract args to find all TokenValue instances.
  We should do a full tree walk, but we will make do with
  a simple top-level scan.  If we fail, validate_otuputs
  will fail, so it's not fatal.
  """
  toks = dict()
  for a in args:
    debug(f'arg {a}')
    if type(a) == TokenValue:
      add_tokens(toks, a.cna, a.num)
  for key in kwargs:
    a = kwargs[key]
    if type(a) == TokenValue:
      add_tokens(toks, a.cna, a.num)
  return toks

class Halt(Exception):
  def __init__(self, retval: object) -> None:
    super().__init__([retval])
    self.retval = retval

class ContractContext:
  def __init__(self, ledger) -> None:
    self.ledger = ledger
    self.ddtm = ledger.time
    self.toks_stack = []
    self.outputs = []
    self.contracts_called = []
  def my_toks(self):
    # return toks top of stack
    return self.toks_stack[len(self.toks_stack)-1]
  def debit_tokens(self, toks: dict):
    bag = self.my_toks()
    debug(f'my bag {bag}')
    for cna in toks:
      num = toks[cna]
      if num != 0:
        bag[cna] = bag.get(cna, 0) - num
        if bag[cna] < 0:
          raise ValidationException(f'negative balance of token type {cna}')
  def halt(self, retval):
    raise(Halt(retval))
  def send(self, pk: PublicKey, toks: dict):
    # !!! TODO: charge a fee?
    debug(f'attempt to send {toks} from {self.my_toks()}')
    self.debit_tokens(toks)
    self.outputs.append(PlainUtxo(pk, toks))
  def deploy(self, contract, toks):
    # !!! TODO: charge a fee?
    self.debit_tokens(toks)
    ensure(CNA.XLOV in self.my_toks() and self.my_toks()[CNA.XLOV] >= MIN_XADA,
          'missing MIN_XADA after send')
    ensure(CNA.XLOV in toks and toks[CNA.XLOV] >= MIN_XADA,
          'deployed contract missing MIN_XADA')
    utxo = ContractUtxo(contract, toks)
    debug(f'deploying {utxo}')
    self.outputs.append(utxo)
    return utxo.hash
  def call(self, contract_hash, m, *args, **kwargs):
    # !!! TODO: charge a fee?
    ensure(contract_hash in self.ledger.utxos_by_hash,
           f'contract not found {contract_hash}')
    # We harvest here, not in call_utxo, because the entry
    # point comes directly into call_utxo and it has no harvest
    self.debit(harvest_toks(args, kwargs))
    ensure(CNA.XLOV in self.my_toks() and self.my_toks()[CNA.XLOV] >= MIN_XADA,
        'missing MIN_XADA after calling another contract')
    callee = self.ledger[contract_hash]
    return self.call_utxo(callee, m, args, kwargs)
  def call_utxo(self, callee, m, args, kwargs):
    ensure(callee not in self.contracts_called,
           'recursion and reentrance forbidden')
    self.contracts_called.append(callee)
    callee.tx_prepare() # create rollback image
    self.toks_stack.append(callee.toks())
    try:
      try:
        retval = callee.contract().call_with_ctx(self, m, args, kwargs)
        # my_toks are still the callee's, since we have not popped yet
        ensure(CNA.XLOV in self.my_toks() and self.my_toks()[CNA.XLOV] >= MIN_XADA,
          'missing MIN_XADA after call')
      except Halt as h:
        retval = h.retval
        debug(f'halt {callee} with retval {retval}')
        # skip adding to called_after; remove from ledger
        self.ledger.remove_utxo(callee)
      self.toks_stack.pop()
      return retval
    except Exception as ex:
      debug(f'exception in call: {ex}')
      # re-raise
      raise ex

class AbstractContract:
  """
  All concrete Xardano contracts must extend AbstractContract
  """
  def __init__(self) -> None:
    self.ctx = None
  # `call_with_ctx` is invoked by ctx
  def call_with_ctx(self, ctx, m, args, kwargs):
    ensure(not self.ctx, 'nested call_with_ctx should not happen')
    self.ctx = ctx
    # consider any tokens passed to this contract as belonging
    # to this contract
    harvested = harvest_toks(args, kwargs)
    debug(f'harvested = {harvested}')
    for cna in harvested:
      add_tokens(ctx.my_toks(), cna, harvested[cna])
    try:
      method = getattr(self, m)
      # invoke the method
      retval = method(*args, **kwargs)
      self.ctx = None
      return retval
    except Exception as ex:
      self.ctx = None
      # re-raise
      raise ex

class CallTx(AbstractTx):
  def __init__(self,
               inputs: list,
               outputs: list,
               contract_hash: bytes,
               m: str,
               args,
               kwargs
               ) -> None:
    super().__init__(inputs, outputs)
    self.contract_hash = contract_hash
    self.m = m
    self.args = args
    self.kwargs = kwargs
  def validate(self, ledger, dttm):
    ctx = ContractContext(ledger)
    ensure(self.contract_hash in ledger.utxos_by_hash,
           f'contract not found {self.contract_hash}')
    contract_utxo = ledger.utxos_by_hash[self.contract_hash]
    retval = None
    try:
      retval = ctx.call_utxo(contract_utxo, self.m, self.args, self.kwargs)
      debug(f'=========== {self.m}(...) => {retval}')
    except Exception as ex:
      debug(f'=========== !!! {self.m}(...) => {ex}')
      self.ctx = None
      for u in ctx.contracts_called:
        u.tx_rollback()
      # re-raise
      raise ex
    # The call succeeded.
    debug(f'all contracts called {ctx.contracts_called}')
    # The rollback image of every called contract is an extra_input
    extra_inputs = [u.tx_preimage() for u in ctx.contracts_called]
    self.validate_inputs(ledger, extra_inputs)
    # The current image of every called contract is an extr_output,
    # as are any explicit outputs such as spends or deploys.
    extra_outputs = ctx.outputs + ctx.contracts_called
    self.validate_outputs(ledger, CALL_TX_FEE, extra_outputs)
    # If we get here, we are ready to commit all changes.
    for u in ctx.contracts_called:
      u.tx_commit()
    for out in ctx.outputs:
      ctx.ledger.add_utxo(out)
    return retval

def wallet_call(self: Wallet,
                contract_hash,
                m: str,
                *args,
                **kwargs
                ):
  #
  # Ah, darn.  How do we know ahead of time what tokens
  # are needed?  We can harvest args and kwargs, but that
  # means we don't levy any fees for internal calls or deploys.
  #
  # The only real fix is to move coin selection into validation,
  # saving input and output validation until after coin selection.
  # I.e., compute all the needed tokens by executing the contract.
  # We could do this more like a real chain -- running the contract
  # both off and on chain -- or we could run the contract just once
  # and embed coin selection in the on-chain validation.
  #
  harvested = harvest_toks(args, kwargs)
  needed = harvested # !!! TODO: include interior fees
  add_tokens(needed, CNA.XLOV, CALL_TX_FEE)
  (inputs, remainders) = self.select_coins(needed)
  outputs = [PlainUtxo(self.pk, remainders)]
  # create and sign the transaction
  tx = CallTx(inputs, outputs, contract_hash, m, args, kwargs)
  tx.sign(self.sign(tx.tx_hash))
  # submit the transaction
  return self.ledger.validate(tx)

# Add method to wallet
Wallet.call = wallet_call

# %%
class XardanoLedger:
  def __init__(self):
    self.utxos_by_hash = dict()
    self.plain_utxos_by_pk = dict()
    self.time = datetime.now()
  def add_utxo(self, utxo):
    if utxo.hash not in self.utxos_by_hash:
      self.utxos_by_hash[utxo.hash] = utxo
    else:
      raise ValidationException(f'duplicate contract utxo {utxo}')
    match utxo:
      case PlainUtxo():
        self.utxos_by_hash[utxo.hash] = utxo
        if utxo.pk not in self.plain_utxos_by_pk:
          self.plain_utxos_by_pk[utxo.pk] = [utxo]
        else:
          self.plain_utxos_by_pk[utxo.pk].append(utxo)
      case ContractUtxo():
        pass
      case _:
        raise ValidationException(f'unhandled utxo type {type(utxo)} in add_utxo')
  def remove_utxo(self, utxo):
    if utxo.hash in self.utxos_by_hash:
      del self.utxos_by_hash[utxo.hash]
    match utxo:
      case PlainUtxo():
        self.plain_utxos_by_pk[utxo.pk].remove(utxo)
      case ContractUtxo():
        pass
      case _:
        raise ValidationException(f'unhandled utxo type {type(utxo)} in remove_utxo')
  def send_faucet_tokens(self, w: Wallet, tv: TokenValue):
    utxo = PlainUtxo(w.pk, {tv.cna : tv.num})
    self.add_utxo(utxo)
  def validate(self, tx):
    rollback = (
        copy(self.utxos_by_hash),
        copy(self.plain_utxos_by_pk)
    )
    try:
      retval = tx.validate(self, self.time)
      self.time = self.time + timedelta(seconds=1)
      return retval
    except ValidationException as ex:
      # time passes anyway
      self.time = self.time + timedelta(seconds=1)
      # restore state
      self.utxos_by_hash, self.plain_utxos_by_pk = rollback
      # reraise exception
      raise ex
  def sleep(self, delta):
    self.time = self.time + delta

