//! A crate for Othello.

#![no_std]

/// A position on a board.
///
/// ```txt
///                       column
///        0    1    2    3    4    5    6    7
///     +----+----+----+----+----+----+----+----+
///   0 | 00 | 01 | 02 | 03 | 04 | 05 | 06 | 07 |
///     +----+----+----+----+----+----+----+----+
///   1 | 08 | 09 | 10 | 11 | 12 | 13 | 14 | 15 |
///     +----+----+----+----+----+----+----+----+
///   2 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 |
///     +----+----+----+----+----+----+----+----+
/// r 3 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 |
/// o   +----+----+----+----+----+----+----+----+
/// w 4 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 |
///     +----+----+----+----+----+----+----+----+
///   5 | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 |
///     +----+----+----+----+----+----+----+----+
///   6 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 |
///     +----+----+----+----+----+----+----+----+
///   7 | 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 |
///     +----+----+----+----+----+----+----+----+
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Position {
    raw: u8,
}

impl Position {
    /// Gets a position from a raw value.
    ///
    /// # Errors
    /// This function will return an error if `raw` is greater than or equal to `64`.
    pub const fn new(raw: u8) -> Result<Self, PositionNewError> {
        match raw < 64 {
            true => Result::Ok(unsafe { Self::new_unchecked(raw) }),
            false => Result::Err(PositionNewError {
                raw,
            }),
        }
    }

    /// Gets a position from a raw value.
    ///
    /// # Safety
    /// `raw` must be lesser than 64.
    pub const unsafe fn new_unchecked(raw: u8) -> Self {
        Self {
            raw,
        }
    }

    /// Gets a position from a row and a column.
    ///
    /// # Errors
    /// This function will return an error if `row` or `column` is greater than or equal to `8`.
    pub const fn at(row: u8, column: u8) -> Result<Self, PositionAtError> {
        match (row < 8, column < 8) {
            (true, true) => Result::Ok(unsafe { Self::at_unchecked(row, column) }),
            _ => Result::Err(PositionAtError {
                row,
                column,
            }),
        }
    }

    /// Gets a position from a row and a column.
    ///
    /// # Safety
    /// `row` and `column` must be lesser than 8.
    pub const unsafe fn at_unchecked(row: u8, column: u8) -> Self {
        Self::new_unchecked(8 * row + column)
    }

    /// Gets a raw value.
    pub const fn as_raw(self) -> u8 {
        self.raw
    }

    /// Gets a row.
    pub const fn row(self) -> u8 {
        self.raw / 8
    }

    /// Gets a column.
    pub const fn column(self) -> u8 {
        self.raw % 8
    }

    /// Gets an iterator of all positions.
    pub fn iter() -> impl Iterator<Item = Self> {
        (0..64).map(|position| unsafe { Self::new_unchecked(position) })
    }
}

/// An error returned by [`Position::new`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PositionNewError {
    raw: u8,
}

/// An error returned by [`Position::at`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PositionAtError {
    row: u8,
    column: u8,
}

/// 8x8 boolean values.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Bools {
    raw: u64,
}

impl Bools {
    const MASK1: Bools = Bools::repeat(false)
        .set(unsafe { Position::at_unchecked(4, 0) }, true)
        .set(unsafe { Position::at_unchecked(4, 1) }, true)
        .set(unsafe { Position::at_unchecked(4, 2) }, true)
        .set(unsafe { Position::at_unchecked(4, 3) }, true)
        .set(unsafe { Position::at_unchecked(5, 0) }, true)
        .set(unsafe { Position::at_unchecked(5, 1) }, true)
        .set(unsafe { Position::at_unchecked(5, 2) }, true)
        .set(unsafe { Position::at_unchecked(5, 3) }, true)
        .set(unsafe { Position::at_unchecked(6, 0) }, true)
        .set(unsafe { Position::at_unchecked(6, 1) }, true)
        .set(unsafe { Position::at_unchecked(6, 2) }, true)
        .set(unsafe { Position::at_unchecked(6, 3) }, true)
        .set(unsafe { Position::at_unchecked(7, 0) }, true)
        .set(unsafe { Position::at_unchecked(7, 1) }, true)
        .set(unsafe { Position::at_unchecked(7, 2) }, true)
        .set(unsafe { Position::at_unchecked(7, 3) }, true);
    const MASK2: Bools = Bools::repeat(false)
        .set(unsafe { Position::at_unchecked(2, 0) }, true)
        .set(unsafe { Position::at_unchecked(2, 1) }, true)
        .set(unsafe { Position::at_unchecked(2, 4) }, true)
        .set(unsafe { Position::at_unchecked(2, 5) }, true)
        .set(unsafe { Position::at_unchecked(3, 0) }, true)
        .set(unsafe { Position::at_unchecked(3, 1) }, true)
        .set(unsafe { Position::at_unchecked(3, 4) }, true)
        .set(unsafe { Position::at_unchecked(3, 5) }, true)
        .set(unsafe { Position::at_unchecked(6, 0) }, true)
        .set(unsafe { Position::at_unchecked(6, 1) }, true)
        .set(unsafe { Position::at_unchecked(6, 4) }, true)
        .set(unsafe { Position::at_unchecked(6, 5) }, true)
        .set(unsafe { Position::at_unchecked(7, 0) }, true)
        .set(unsafe { Position::at_unchecked(7, 1) }, true)
        .set(unsafe { Position::at_unchecked(7, 4) }, true)
        .set(unsafe { Position::at_unchecked(7, 5) }, true);
    const MASK3: Bools = Bools::repeat(false)
        .set(unsafe { Position::at_unchecked(1, 0) }, true)
        .set(unsafe { Position::at_unchecked(1, 2) }, true)
        .set(unsafe { Position::at_unchecked(1, 4) }, true)
        .set(unsafe { Position::at_unchecked(1, 6) }, true)
        .set(unsafe { Position::at_unchecked(3, 0) }, true)
        .set(unsafe { Position::at_unchecked(3, 2) }, true)
        .set(unsafe { Position::at_unchecked(3, 4) }, true)
        .set(unsafe { Position::at_unchecked(3, 6) }, true)
        .set(unsafe { Position::at_unchecked(5, 0) }, true)
        .set(unsafe { Position::at_unchecked(5, 2) }, true)
        .set(unsafe { Position::at_unchecked(5, 4) }, true)
        .set(unsafe { Position::at_unchecked(5, 6) }, true)
        .set(unsafe { Position::at_unchecked(7, 0) }, true)
        .set(unsafe { Position::at_unchecked(7, 2) }, true)
        .set(unsafe { Position::at_unchecked(7, 4) }, true)
        .set(unsafe { Position::at_unchecked(7, 6) }, true);
    const MASK4: Self = Self::repeat(true)
        .set(unsafe { Position::at_unchecked(0, 0) }, false)
        .set(unsafe { Position::at_unchecked(0, 7) }, false)
        .set(unsafe { Position::at_unchecked(1, 0) }, false)
        .set(unsafe { Position::at_unchecked(1, 7) }, false)
        .set(unsafe { Position::at_unchecked(2, 0) }, false)
        .set(unsafe { Position::at_unchecked(2, 7) }, false)
        .set(unsafe { Position::at_unchecked(3, 0) }, false)
        .set(unsafe { Position::at_unchecked(3, 7) }, false)
        .set(unsafe { Position::at_unchecked(4, 0) }, false)
        .set(unsafe { Position::at_unchecked(4, 7) }, false)
        .set(unsafe { Position::at_unchecked(5, 0) }, false)
        .set(unsafe { Position::at_unchecked(5, 7) }, false)
        .set(unsafe { Position::at_unchecked(6, 0) }, false)
        .set(unsafe { Position::at_unchecked(6, 7) }, false)
        .set(unsafe { Position::at_unchecked(7, 0) }, false)
        .set(unsafe { Position::at_unchecked(7, 7) }, false);
    const MASK5: Self = Self::repeat(true)
        .set(unsafe { Position::at_unchecked(0, 0) }, false)
        .set(unsafe { Position::at_unchecked(0, 1) }, false)
        .set(unsafe { Position::at_unchecked(0, 2) }, false)
        .set(unsafe { Position::at_unchecked(0, 3) }, false)
        .set(unsafe { Position::at_unchecked(0, 4) }, false)
        .set(unsafe { Position::at_unchecked(0, 5) }, false)
        .set(unsafe { Position::at_unchecked(0, 6) }, false)
        .set(unsafe { Position::at_unchecked(0, 7) }, false)
        .set(unsafe { Position::at_unchecked(7, 0) }, false)
        .set(unsafe { Position::at_unchecked(7, 1) }, false)
        .set(unsafe { Position::at_unchecked(7, 2) }, false)
        .set(unsafe { Position::at_unchecked(7, 3) }, false)
        .set(unsafe { Position::at_unchecked(7, 4) }, false)
        .set(unsafe { Position::at_unchecked(7, 5) }, false)
        .set(unsafe { Position::at_unchecked(7, 6) }, false)
        .set(unsafe { Position::at_unchecked(7, 7) }, false);
    const MASK6: Self = Self::and(Self::MASK4, Self::MASK5);

    /// Gets boolean values from a raw value.
    pub const fn new(raw: u64) -> Self {
        Self {
            raw,
        }
    }

    /// Gets boolean values which are equal to the value.
    pub const fn repeat(value: bool) -> Self {
        match value {
            false => Self::new(0),
            true => Self::repeat(false).not(),
        }
    }

    /// Gets a raw value.
    pub const fn as_raw(self) -> u64 {
        self.raw
    }

    /// Tests if the values are equal.
    pub const fn equal(self, other: Self) -> bool {
        self.raw == other.raw
    }

    /// Calculates bitwise NOT.
    pub const fn not(self) -> Self {
        Self::new(!self.raw)
    }

    /// Calculates bitwise AND.
    pub const fn and(self, other: Self) -> Self {
        Self::new(self.raw & other.raw)
    }

    /// Calculates bitwise OR.
    pub const fn or(self, other: Self) -> Self {
        Self::new(self.raw | other.raw)
    }

    /// Calculates bitwise XOR.
    pub const fn xor(self, other: Self) -> Self {
        Self::new(self.raw ^ other.raw)
    }

    /// Shifts the bits to the left.
    pub const fn shl(self, n: u8) -> Self {
        Self::new(self.raw << n)
    }

    /// Shifts the bits to the right.
    pub const fn shr(self, n: u8) -> Self {
        Self::new(self.raw >> n)
    }

    /// Gets a boolean value at the position.
    pub const fn get(self, position: Position) -> bool {
        !self.and(Self::repeat(false).set(position, true)).all(false)
    }

    /// Sets a boolean value at the position.
    pub const fn set(self, position: Position, value: bool) -> Self {
        let position = Self::new(1 << position.as_raw());

        match value {
            true => self.or(position),
            false => self.and(position.not()),
        }
    }

    pub const fn all(self, value: bool) -> bool {
        self.equal(Self::repeat(value))
    }

    /// Counts boolean values which are equal to the argument.
    pub const fn count(self, value: bool) -> u32 {
        match value {
            true => self.raw.count_ones(),
            false => self.raw.count_zeros(),
        }
    }

    /// Moves boolean values at `(r, c)` to `(7 - r, c)`.
    pub const fn flip_vertically(self) -> Self {
        Self::new(self.raw.swap_bytes())
    }

    /// Moves boolean values at `(r, c)` to `(c, r)`.
    pub const fn flip_diagonally(self) -> Self {
        macro_rules! calc {
            ($bits:expr, $mask:expr, $n:expr) => {{
                let mask = $mask.and($bits.xor($bits.shl($n)));
                mask.xor(mask.shr($n))
            }};
        }

        let mut result = self;
        result = result.xor(calc!(result, Self::MASK1, 28));
        result = result.xor(calc!(result, Self::MASK2, 14));
        result = result.xor(calc!(result, Self::MASK3, 7));
        result
    }

    /// Moves boolean values at `(r, c)` to `(7 - r, 7 - c)`.
    pub const fn rotate(self) -> Self {
        Self::new(self.raw.reverse_bits())
    }

    /// Calculates equal values without flipping and rotation.
    pub const fn augment(self) -> [Self; 8] {
        let mut result = [self; 8];
        result[4] = result[4].flip_diagonally();
        result[5] = result[4];
        result[6] = result[4];
        result[7] = result[4];
        result[2] = result[2].rotate();
        result[3] = result[2];
        result[6] = result[6].rotate();
        result[7] = result[6];
        result[1] = result[1].flip_vertically();
        result[3] = result[3].flip_vertically();
        result[5] = result[5].flip_vertically();
        result[7] = result[7].flip_vertically();
        result
    }

    /// Gets positions where the boolean value is equal to the argument.
    pub fn positions(self, value: bool) -> impl Iterator<Item = Position> {
        match value {
            true => Position::iter().filter(move |position| self.get(*position)),
            false => self.not().positions(true),
        }
    }
}

macro_rules! line {
    ($start:expr, $area:expr, $shift:ident, $n:expr) => {{
        let mut result = $start.$shift($n).and($area);
        result = result.$shift($n).and($area).or(result);
        result = result.$shift($n).and($area).or(result);
        result = result.$shift($n).and($area).or(result);
        result = result.$shift($n).and($area).or(result);
        result.$shift($n).and($area).or(result)
    }};
}

/// A player.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Player {
    Black,
    White,
}

impl Player {
    /// Gets the opponent.
    pub const fn opponent(self) -> Self {
        match self {
            Self::Black => Self::White,
            Self::White => Self::Black,
        }
    }
}

/// A board.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Board {
    black: Bools,
    white: Bools,
}

impl Board {
    /// The standard board.
    pub const STANDARD: Self = unsafe {
        Self::new_unchecked(
            Bools::repeat(false)
                .set(Position::at_unchecked(3, 4), true)
                .set(Position::at_unchecked(4, 3), true),
            Bools::repeat(false)
                .set(Position::at_unchecked(3, 3), true)
                .set(Position::at_unchecked(4, 4), true),
        )
    };

    /// Gets a new board.
    ///
    /// Errors
    /// This function will return an error if there is any position which the boolean values of `black` and `white` are true.
    pub const fn new(black: Bools, white: Bools) -> Result<Self, BoardNewError> {
        match Bools::and(black, white).all(false) {
            true => Result::Ok(unsafe { Self::new_unchecked(black, white) }),
            false => Result::Err(BoardNewError {
                black,
                white,
            }),
        }
    }

    /// Gets a new board.
    ///
    /// # Safety
    /// The all boolean values of `black` AND `white` must be false.
    pub const unsafe fn new_unchecked(black: Bools, white: Bools) -> Self {
        Self {
            black,
            white,
        }
    }

    /// Gets a board with black and white swaped.
    pub const fn swap_disks(self) -> Self {
        unsafe { Self::new_unchecked(self.white, self.black) }
    }

    /// Gets disks.
    pub const fn disks(self, player: Player) -> Bools {
        match player {
            Player::Black => self.black,
            Player::White => self.white,
        }
    }

    /// Gets a color of the disk at the position.
    pub const fn get(self, position: Position) -> Option<Player> {
        if self.black.get(position) {
            Option::Some(Player::Black)
        } else if self.white.get(position) {
            Option::Some(Player::White)
        } else {
            Option::None
        }
    }

    /// Calculates legal moves.
    pub const fn legal_moves(self, player: Player) -> Bools {
        match player {
            Player::Black => {
                macro_rules! calc {
                    ($board:expr, $mask:expr, $n:expr) => {{
                        let mask = $board.white.and($mask);

                        Bools::or(
                            line!($board.black, mask, shl, $n).shl($n),
                            line!($board.black, mask, shr, $n).shr($n),
                        )
                    }};
                }

                Bools::repeat(false)
                    .or(calc!(self, Bools::MASK4, 1))
                    .or(calc!(self, Bools::MASK6, 7))
                    .or(calc!(self, Bools::MASK5, 8))
                    .or(calc!(self, Bools::MASK6, 9))
                    .and(Bools::or(self.black, self.white).not())
            },
            Player::White => self.swap_disks().legal_moves(Player::Black),
        }
    }

    /// Calculates disks which will be reversed.
    pub const fn reversed_disks(self, player: Player, position: Position) -> Bools {
        match player {
            Player::Black => {
                macro_rules! calc {
                    ($board:expr, $position:expr, $mask:expr, $n:expr) => {{
                        let mask = $board.white.and($mask);
                        let mut result = Bools::repeat(false);
                        let line = line!($position, mask, shl, $n);

                        if !$board.black.and(line.shl($n)).all(false) {
                            result = result.or(line);
                        }

                        let line = line!($position, mask, shr, $n);

                        if !$board.black.and(line.shr($n)).all(false) {
                            result = result.or(line);
                        }

                        result
                    }};
                }

                let position = Bools::repeat(false).set(position, true);

                Bools::repeat(false)
                    .or(calc!(self, position, Bools::MASK4, 1))
                    .or(calc!(self, position, Bools::MASK6, 7))
                    .or(calc!(self, position, Bools::MASK5, 8))
                    .or(calc!(self, position, Bools::MASK6, 9))
            },
            Player::White => self.swap_disks().reversed_disks(Player::Black, position),
        }
    }

    /// Makes a move.
    ///
    /// # Errors
    /// This function will return an error if the move is illegal.
    pub const fn make_move(
        self,
        player: Player,
        position: Position,
    ) -> Result<Self, BoardMakeMoveError> {
        match self.legal_moves(player).get(position) {
            true => Result::Ok(unsafe { self.make_move_unchecked(player, position) }),
            false => Result::Err(BoardMakeMoveError {
                color: player,
                position,
            }),
        }
    }

    /// Makes a move.
    ///
    /// # Errors
    /// This function will return an error if there is a disk at the position.
    pub const fn make_move_illegally(
        self,
        player: Player,
        position: Position,
    ) -> Result<Self, BoardMakeMoveIllegallyError> {
        match self.get(position) {
            Option::None => Result::Ok(unsafe { self.make_move_unchecked(player, position) }),
            Option::Some(_) => Result::Err(BoardMakeMoveIllegallyError {
                color: player,
                position,
            }),
        }
    }

    /// Makes a move.
    ///
    /// # Safety
    /// There be must no disk at the position.
    pub const unsafe fn make_move_unchecked(self, player: Player, position: Position) -> Self {
        match player {
            Player::Black => {
                let reversed = self.reversed_disks(Player::Black, position);

                Self::new_unchecked(
                    self.black
                        .xor(Bools::repeat(false).set(position, true))
                        .xor(reversed),
                    self.white.xor(reversed),
                )
            },
            Player::White => self
                .swap_disks()
                .make_move_unchecked(Player::Black, position)
                .swap_disks(),
        }
    }

    /// Tests if the game is ongoing.
    pub const fn is_ongoing(self) -> bool {
        !self.legal_moves(Player::Black).all(false) | !self.legal_moves(Player::White).all(false)
    }

    /// Returns the current winner, or none when the result is draw.
    pub const fn winner(self) -> Option<Player> {
        let black = self.black.count(true);
        let white = self.white.count(true);

        if black > white {
            Option::Some(Player::Black)
        } else if black < white {
            Option::Some(Player::White)
        } else {
            Option::None
        }
    }
}

/// An error returned by [`Board::new`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BoardNewError {
    black: Bools,
    white: Bools,
}

/// An error returned by [`Board::make_move`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BoardMakeMoveError {
    color: Player,
    position: Position,
}

/// An error returned by [`Board::make_move_illegally`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BoardMakeMoveIllegallyError {
    color: Player,
    position: Position,
}

/// A game.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Game {
    board: Board,
    next: Player,
}

impl Game {
    /// The standard game.
    pub const STANDARD: Self = Self::new(Board::STANDARD, Player::Black);

    /// Gets a new game.
    pub const fn new(board: Board, next: Player) -> Self {
        Self {
            board,
            next,
        }
    }

    /// Gets the board.
    pub const fn board(self) -> Board {
        self.board
    }

    /// Gets the next player.
    pub const fn next(self) -> Player {
        self.next
    }

    /// Calculates legal moves.
    pub const fn legal_moves(self) -> Bools {
        self.board.legal_moves(self.next)
    }

    /// Calculates disks which will be reversed.
    pub const fn reversed_disks(self, position: Position) -> Bools {
        self.board.reversed_disks(self.next, position)
    }

    /// Make a move.
    ///
    /// # Errors
    /// See [`Board::make_move`].
    pub const fn make_move(self, position: Position) -> Result<Self, BoardMakeMoveError> {
        match self.board.make_move(self.next, position) {
            Result::Ok(board) => Result::Ok(Self::new(board, self.next.opponent())),
            Result::Err(error) => Result::Err(error),
        }
    }

    /// Make a move.
    ///
    /// # Errors
    /// See [`Board::make_move_illegally`]
    pub const fn make_move_illegally(
        self,
        position: Position,
    ) -> Result<Self, BoardMakeMoveIllegallyError> {
        match self.board.make_move_illegally(self.next, position) {
            Result::Ok(board) => Result::Ok(Self::new(board, self.next.opponent())),
            Result::Err(error) => Result::Err(error),
        }
    }

    /// Make a move.
    ///
    /// # Safety
    /// See [`Board::make_move_unchecked`].
    pub const unsafe fn make_move_unchecked(self, position: Position) -> Self {
        Self::new(
            self.board.make_move_unchecked(self.next, position),
            self.next.opponent(),
        )
    }

    /// Passes the turn.
    pub const fn pass_turn(self) -> Self {
        Self::new(self.board, self.next.opponent())
    }
}
