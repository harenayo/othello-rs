//! A crate for Othello.

#![no_std]

/// A position of a board.
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
    value: u8,
}

impl Position {
    /// Gets a position.
    ///
    /// # Errors
    /// This function will return an error if `value` is greater than `64`.
    pub const fn of(value: u8) -> Result<Self, PositionOfError> {
        match value < 64 {
            true => Result::Ok(unsafe { Self::of_unchecked(value) }),
            false => Result::Err(PositionOfError {
                value,
            }),
        }
    }

    /// Gets a position.
    ///
    /// # Safety
    /// `value` must be lesser than 64.
    pub const unsafe fn of_unchecked(value: u8) -> Self {
        Self {
            value,
        }
    }

    /// Gets a position.
    ///
    /// # Errors
    /// This function will return an error if `row` or `column` is greater than `8`.
    pub const fn at(row: u8, column: u8) -> Result<Self, PositionAtError> {
        match (row < 8, column < 8) {
            (true, true) => Result::Ok(unsafe { Self::at_unchecked(row, column) }),
            _ => Result::Err(PositionAtError {
                row,
                column,
            }),
        }
    }

    /// Gets a position.
    ///
    /// # Safety
    /// `row` and `column` must be lesser than 8.
    pub const unsafe fn at_unchecked(row: u8, column: u8) -> Self {
        Self::of_unchecked(8 * row + column)
    }

    /// Gets a raw value.
    pub const fn value(self) -> u8 {
        self.value
    }

    /// Calculates a row number.
    pub const fn row(self) -> u8 {
        self.value / 8
    }

    /// Calculates a column number.
    pub const fn column(self) -> u8 {
        self.value % 8
    }

    /// Gets an iterator of all positions.
    pub fn iter() -> impl Iterator<Item = Self> {
        (0..64).map(|position| unsafe { Self::of_unchecked(position) })
    }
}

/// An error returned by [`Position::of`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PositionOfError {
    value: u8,
}

/// An error returned by [`Position::at`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PositionAtError {
    row: u8,
    column: u8,
}

/// 64-bit data of a board.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Bits {
    value: u64,
}

impl Bits {
    const MASK_ALL_EDGES: Self = Self::and(Self::MASK_RIGHT_LEFT, Self::MASK_TOP_BOTTOM);
    const MASK_RIGHT_LEFT: Self = Self::of(0)
        .set(unsafe { Position::at_unchecked(0, 0) }, true)
        .set(unsafe { Position::at_unchecked(0, 7) }, true)
        .set(unsafe { Position::at_unchecked(1, 0) }, true)
        .set(unsafe { Position::at_unchecked(1, 7) }, true)
        .set(unsafe { Position::at_unchecked(2, 0) }, true)
        .set(unsafe { Position::at_unchecked(2, 7) }, true)
        .set(unsafe { Position::at_unchecked(3, 0) }, true)
        .set(unsafe { Position::at_unchecked(3, 7) }, true)
        .set(unsafe { Position::at_unchecked(4, 0) }, true)
        .set(unsafe { Position::at_unchecked(4, 7) }, true)
        .set(unsafe { Position::at_unchecked(5, 0) }, true)
        .set(unsafe { Position::at_unchecked(5, 7) }, true)
        .set(unsafe { Position::at_unchecked(6, 0) }, true)
        .set(unsafe { Position::at_unchecked(6, 7) }, true)
        .set(unsafe { Position::at_unchecked(7, 0) }, true)
        .set(unsafe { Position::at_unchecked(7, 7) }, true)
        .not();
    const MASK_TOP_BOTTOM: Self = Self::of(0)
        .set(unsafe { Position::at_unchecked(0, 0) }, true)
        .set(unsafe { Position::at_unchecked(0, 1) }, true)
        .set(unsafe { Position::at_unchecked(0, 2) }, true)
        .set(unsafe { Position::at_unchecked(0, 3) }, true)
        .set(unsafe { Position::at_unchecked(0, 4) }, true)
        .set(unsafe { Position::at_unchecked(0, 5) }, true)
        .set(unsafe { Position::at_unchecked(0, 6) }, true)
        .set(unsafe { Position::at_unchecked(0, 7) }, true)
        .set(unsafe { Position::at_unchecked(7, 0) }, true)
        .set(unsafe { Position::at_unchecked(7, 1) }, true)
        .set(unsafe { Position::at_unchecked(7, 2) }, true)
        .set(unsafe { Position::at_unchecked(7, 3) }, true)
        .set(unsafe { Position::at_unchecked(7, 4) }, true)
        .set(unsafe { Position::at_unchecked(7, 5) }, true)
        .set(unsafe { Position::at_unchecked(7, 6) }, true)
        .set(unsafe { Position::at_unchecked(7, 7) }, true)
        .not();

    /// Gets bits.
    pub const fn of(value: u64) -> Self {
        Self {
            value,
        }
    }

    /// Gets a raw value.
    pub const fn value(self) -> u64 {
        self.value
    }

    /// Calculates bitwise NOT.
    pub const fn not(self) -> Self {
        Self::of(!self.value)
    }

    /// Calculates bitwise AND.
    pub const fn and(self, other: Self) -> Self {
        Self::of(self.value & other.value)
    }

    /// Calculates bitwise OR.
    pub const fn or(self, other: Self) -> Self {
        Self::of(self.value | other.value)
    }

    /// Calculates bitwise XOR.
    pub const fn xor(self, other: Self) -> Self {
        Self::of(self.value ^ other.value)
    }

    /// Shifts the bits to the left.
    pub const fn shl(self, n: u8) -> Self {
        Self::of(self.value << n)
    }

    /// Shifts the bits to the right.
    pub const fn shr(self, n: u8) -> Self {
        Self::of(self.value >> n)
    }

    /// Gets a bit.
    pub const fn get(self, position: Position) -> bool {
        self.and(Self::of(0).set(position, true)).any()
    }

    /// Sets a bit.
    pub const fn set(self, position: Position, value: bool) -> Self {
        let position = Self::of(1 << position.value());

        match value {
            true => self.or(position),
            false => self.and(position.not()),
        }
    }

    /// Moves a bit at (r, c) to (7 - r, c).
    pub const fn flip_vertically(self) -> Self {
        Self::of(self.value.swap_bytes())
    }

    /// Moves a bit at (r, c) to (c, r).
    pub const fn flip_diagonally(self) -> Self {
        const MASK1: Bits = Bits::of(0)
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
        const MASK2: Bits = Bits::of(0)
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
        const MASK3: Bits = Bits::of(0)
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

        macro_rules! calc {
            ($bits:expr, $mask:expr, $n:expr) => {{
                let mask = $mask.and($bits.xor($bits.shl($n)));
                mask.xor(mask.shr($n))
            }};
        }

        let mut result = self;
        result = result.xor(calc!(result, MASK1, 28));
        result = result.xor(calc!(result, MASK2, 14));
        result = result.xor(calc!(result, MASK3, 7));
        result
    }

    /// Moves a bit at (r, c) to (7 - r, 7 - c).
    pub const fn rotate(self) -> Self {
        Self::of(self.value.reverse_bits())
    }

    /// Calculates same bits without flipping and rotation.
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

    /// Tests if any bit is true.
    pub const fn any(self) -> bool {
        self.value != 0
    }

    /// Counts bits which are equal to the argument.
    pub const fn count(self, value: bool) -> u32 {
        match value {
            true => self.value.count_ones(),
            false => self.value.count_zeros(),
        }
    }

    /// Gets positions where the bit is equal to the argument.
    pub fn positions(self, value: bool) -> impl Iterator<Item = Position> {
        match value {
            true => Position::iter().filter(move |position| self.get(*position)),
            false => self.not().positions(true),
        }
    }
}

macro_rules! line {
    ($bits:expr, $mask:expr, $shift:ident, $n:expr) => {{
        let mut result = $bits.$shift($n).and($mask);
        result = result.$shift($n).and($mask).or(result);
        result = result.$shift($n).and($mask).or(result);
        result = result.$shift($n).and($mask).or(result);
        result = result.$shift($n).and($mask).or(result);
        result = result.$shift($n).and($mask).or(result);
        result
    }};
}

/// The colors, black or white.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Color {
    Black,
    White,
}

impl Color {
    /// Gets the another color.
    pub const fn flip(self) -> Self {
        match self {
            Self::Black => Self::White,
            Self::White => Self::Black,
        }
    }
}

/// The result kind, win or lose.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ResultKind {
    Win,
    Lose,
}

impl ResultKind {
    /// Gets the another kind.
    pub const fn flip(self) -> Self {
        match self {
            Self::Win => Self::Lose,
            Self::Lose => Self::Win,
        }
    }
}

/// A board.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Board {
    black: Bits,
    white: Bits,
}

impl Board {
    /// The standard board.
    pub const STANDARD: Self = unsafe {
        Self::new_unchecked(
            Bits::of(0)
                .set(Position::at_unchecked(3, 4), true)
                .set(Position::at_unchecked(4, 3), true),
            Bits::of(0)
                .set(Position::at_unchecked(3, 3), true)
                .set(Position::at_unchecked(4, 4), true),
        )
    };

    /// Gets a new board.
    ///
    /// Errors
    /// This function will return an error if there is any position which the bit of `black` and the bit of `white` are true.
    pub const fn new(black: Bits, white: Bits) -> Result<Self, BoardNewError> {
        match Bits::and(black, white).value() {
            0 => Result::Ok(unsafe { Self::new_unchecked(black, white) }),
            _ => Result::Err(BoardNewError {
                black,
                white,
            }),
        }
    }

    /// Gets a new board.
    ///
    /// # Safety
    /// `black` and `white` must be exclusive, in the other words, `black` AND `white` must be `0`.
    pub const unsafe fn new_unchecked(black: Bits, white: Bits) -> Self {
        Self {
            black,
            white,
        }
    }

    /// Gets disks.
    pub const fn disks(self, color: Color) -> Bits {
        match color {
            Color::Black => self.black,
            Color::White => self.white,
        }
    }

    /// Gets a color of a disk at `position`.
    pub const fn get(self, position: Position) -> Option<Color> {
        if self.black.get(position) {
            Option::Some(Color::Black)
        } else if self.white.get(position) {
            Option::Some(Color::White)
        } else {
            Option::None
        }
    }

    /// Calculates legal moves.
    pub const fn legal_moves(self, color: Color) -> Bits {
        macro_rules! calc {
            ($player:expr, $opponent:expr, $mask:expr, $n:expr) => {{
                let mask = $opponent.and($mask);

                Bits::or(
                    line!($player, mask, shl, $n).shl($n),
                    line!($player, mask, shr, $n).shr($n),
                )
            }};
        }

        let player = self.disks(color);
        let opponent = self.disks(color.flip());

        Bits::of(0)
            .or(calc!(player, opponent, Bits::MASK_RIGHT_LEFT, 1))
            .or(calc!(player, opponent, Bits::MASK_ALL_EDGES, 7))
            .or(calc!(player, opponent, Bits::MASK_TOP_BOTTOM, 8))
            .or(calc!(player, opponent, Bits::MASK_ALL_EDGES, 9))
            .and(Bits::or(player, opponent).not())
    }

    /// Calculates disks which will be reversed.
    pub const fn reversed_disks(self, color: Color, position: Position) -> Bits {
        macro_rules! calc {
            ($player:expr, $opponent:expr, $position:expr, $mask:expr, $n:expr) => {{
                let mask = $opponent.and($mask);
                let mut result = Bits::of(0);
                let line = line!($position, mask, shl, $n);

                if $player.and(line.shl($n)).any() {
                    result = result.or(line);
                }

                let line = line!($position, mask, shr, $n);

                if $player.and(line.shr($n)).any() {
                    result = result.or(line);
                }

                result
            }};
        }

        let player = self.disks(color);
        let opponent = self.disks(color.flip());
        let position = Bits::of(0).set(position, true);

        Bits::of(0)
            .or(calc!(player, opponent, position, Bits::MASK_RIGHT_LEFT, 1))
            .or(calc!(player, opponent, position, Bits::MASK_ALL_EDGES, 7))
            .or(calc!(player, opponent, position, Bits::MASK_TOP_BOTTOM, 8))
            .or(calc!(player, opponent, position, Bits::MASK_ALL_EDGES, 9))
    }

    /// Makes a move.
    ///
    /// # Errors
    /// This function will return an error if the move is not legal.
    pub const fn make_move(
        self,
        color: Color,
        position: Position,
    ) -> Result<Self, BoardMakeMoveError> {
        match self.legal_moves(color).get(position) {
            true => Result::Ok(unsafe { self.make_move_unchecked(color, position) }),
            false => Result::Err(BoardMakeMoveError {
                color,
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
        color: Color,
        position: Position,
    ) -> Result<Self, BoardMakeMoveIllegallyError> {
        match self.get(position) {
            Option::None => Result::Ok(unsafe { self.make_move_unchecked(color, position) }),
            Option::Some(_) => Result::Err(BoardMakeMoveIllegallyError {
                color,
                position,
            }),
        }
    }

    /// Makes a move.
    ///
    /// # Safety
    /// There be must no disk at the position.
    pub const unsafe fn make_move_unchecked(self, color: Color, position: Position) -> Self {
        let reversed = self.reversed_disks(color, position);

        let player = self
            .disks(color)
            .xor(Bits::of(0).set(position, true))
            .xor(reversed);

        let opponent = self.disks(color.flip()).xor(reversed);

        match color {
            Color::Black => Self::new_unchecked(player, opponent),
            Color::White => Self::new_unchecked(opponent, player),
        }
    }

    /// Tests if the game is finished.
    pub const fn is_finished(self) -> bool {
        self.legal_moves(Color::Black).any() | self.legal_moves(Color::White).any()
    }

    /// Gets the "now" result of a player.
    pub const fn result(self, color: Color) -> Option<ResultKind> {
        let player = self.disks(color).count(true);
        let opponent = self.disks(color.flip()).count(true);

        if player > opponent {
            Option::Some(ResultKind::Win)
        } else if player < opponent {
            Option::Some(ResultKind::Lose)
        } else {
            Option::None
        }
    }

    /// Gets a player who has the result now.
    pub const fn who(self, result: ResultKind) -> Option<Color> {
        match self.result(Color::Black) {
            Option::Some(black_result) => match (result, black_result) {
                (ResultKind::Win, ResultKind::Win) | (ResultKind::Lose, ResultKind::Lose) => {
                    Option::Some(Color::Black)
                },
                (ResultKind::Win, ResultKind::Lose) | (ResultKind::Lose, ResultKind::Win) => {
                    Option::Some(Color::White)
                },
            },
            Option::None => Option::None,
        }
    }
}

/// An error returned by [`Board::new`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BoardNewError {
    black: Bits,
    white: Bits,
}

/// An error returned by [`Board::make_move`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BoardMakeMoveError {
    color: Color,
    position: Position,
}

/// An error returned by [`Board::make_move_illegally`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BoardMakeMoveIllegallyError {
    color: Color,
    position: Position,
}

/// A game.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Game {
    board: Board,
    next: Color,
}

impl Game {
    /// The standard game.
    pub const STANDARD: Self = Self::new(Board::STANDARD, Color::Black);

    /// Gets a new game.
    pub const fn new(board: Board, next: Color) -> Self {
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
    pub const fn next(self) -> Color {
        self.next
    }

    /// Calculates legal moves.
    pub const fn legal_moves(self) -> Bits {
        self.board.legal_moves(self.next)
    }

    /// Calculates disks which will be reversed.
    pub const fn reversed_disks(self, position: Position) -> Bits {
        self.board.reversed_disks(self.next, position)
    }

    /// Make a move.
    ///
    /// # Errors
    /// See [`Board::make_move`].
    pub const fn make_move(self, position: Position) -> Result<Self, BoardMakeMoveError> {
        match self.board.make_move(self.next, position) {
            Result::Ok(board) => Result::Ok(Self::new(board, self.next.flip())),
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
            Result::Ok(board) => Result::Ok(Self::new(board, self.next.flip())),
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
            self.next.flip(),
        )
    }

    /// Passes a turn.
    pub const fn pass(self) -> Self {
        Self::new(self.board, self.next.flip())
    }
}
