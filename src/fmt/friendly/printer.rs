#![allow(warnings)]

use core::time::Duration as UnsignedDuration;

use alloc::string::String;

use crate::{
    error::err,
    fmt::{
        util::{DecimalFormatter, FractionalFormatter},
        Write, WriteExt,
    },
    util::{rangeint::RFrom, t},
    Error, SignedDuration, Span, Unit,
};

const SECS_PER_HOUR: i64 = MINS_PER_HOUR * SECS_PER_MIN;
const SECS_PER_MIN: i64 = 60;
const MINS_PER_HOUR: i64 = 60;
const NANOS_PER_HOUR: i128 =
    (SECS_PER_MIN * MINS_PER_HOUR * NANOS_PER_SEC) as i128;
const NANOS_PER_MIN: i128 = (SECS_PER_MIN * NANOS_PER_SEC) as i128;
const NANOS_PER_SEC: i64 = 1_000_000_000;
const NANOS_PER_MILLI: i32 = 1_000_000;
const NANOS_PER_MICRO: i32 = 1_000;

/// TODO
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum Designator {
    /// TODO
    Verbose,
    /// TODO
    Short,
    /// TODO
    Compact,
}

/// TODO
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum Spacing {
    /// TODO
    None,
    /// TODO
    BetweenUnits,
    /// TODO
    BetweenUnitsAndDesignators,
}

impl Spacing {
    fn between_units(self) -> &'static str {
        match self {
            Spacing::None => "",
            Spacing::BetweenUnits => " ",
            Spacing::BetweenUnitsAndDesignators => " ",
        }
    }

    fn between_value_and_designator(self) -> &'static str {
        match self {
            Spacing::None => "",
            Spacing::BetweenUnits => "",
            Spacing::BetweenUnitsAndDesignators => " ",
        }
    }
}

/// Controls how the sign, if at all, is included in the formatte duration.
///
/// When using the "hours-minutes-seconds" format, `Auto` and `Suffix` are
/// both treated as equivalent to `Sign`.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum Direction {
    /// Sets the sign format based on other configuration options.
    ///
    /// When [`SpanPrinter::spacing`] is set to [`Spacing::None`], then
    /// `Auto` is equivalent to `Sign`. In all other cases, `Auto` is
    /// equivalent to `Suffix`.
    ///
    /// This is default used by [`SpanPrinter`].
    Auto,
    /// When set, a sign is only written when the span or duration is negative.
    /// And when it is written, it is written as a prefix of the formatted
    /// duration.
    Sign,
    /// A sign is always written, with `-` for negative spans and `+` for all
    /// non-negative spans. The sign is always written as a prefix of the
    /// formatted duration.
    ForceSign,
    /// When set, a sign is only written when the span or duration is negative.
    /// And when it is written, it is written as a suffix via a trailing ` ago`
    /// string.
    Suffix,
}

impl Direction {
    fn sign(self, spacing: Spacing, signum: i8) -> Option<DirectionSign> {
        match self {
            Direction::Auto => match spacing {
                Spacing::None => {
                    if signum < 0 {
                        Some(DirectionSign::Prefix("-"))
                    } else {
                        None
                    }
                }
                Spacing::BetweenUnits
                | Spacing::BetweenUnitsAndDesignators => {
                    if signum < 0 {
                        Some(DirectionSign::Suffix(" ago"))
                    } else {
                        None
                    }
                }
            },
            Direction::Sign => {
                if signum < 0 {
                    Some(DirectionSign::Prefix("-"))
                } else {
                    None
                }
            }
            Direction::ForceSign => {
                Some(DirectionSign::Prefix(if signum < 0 { "-" } else { "+" }))
            }
            Direction::Suffix => {
                if signum < 0 {
                    Some(DirectionSign::Suffix(" ago"))
                } else {
                    None
                }
            }
        }
    }
}

/// The sign to write and whether it should be a prefix or a suffix.
#[derive(Clone, Copy, Debug)]
enum DirectionSign {
    Prefix(&'static str),
    Suffix(&'static str),
}

/// TODO
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum FractionalUnit {
    /// TODO
    ///
    /// NOTE: May drop precision.
    Hour,
    /// TODO
    ///
    /// NOTE: May drop precision.
    Minute,
    /// TODO
    Second,
    /// TODO
    Millisecond,
    /// TODO
    Microsecond,
}

impl From<FractionalUnit> for Unit {
    fn from(u: FractionalUnit) -> Unit {
        match u {
            FractionalUnit::Hour => Unit::Hour,
            FractionalUnit::Minute => Unit::Minute,
            FractionalUnit::Second => Unit::Second,
            FractionalUnit::Millisecond => Unit::Millisecond,
            FractionalUnit::Microsecond => Unit::Microsecond,
        }
    }
}

/// TODO
#[derive(Clone, Debug)]
pub struct SpanPrinter {
    designator: Designator,
    spacing: Spacing,
    direction: Direction,
    fractional: Option<FractionalUnit>,
    comma: bool,
    hms: bool,
    padding: Option<u8>,
    precision: Option<u8>,
}

impl SpanPrinter {
    /// TODO
    #[inline]
    pub const fn new() -> SpanPrinter {
        SpanPrinter {
            designator: Designator::Short,
            spacing: Spacing::BetweenUnits,
            direction: Direction::Auto,
            fractional: None,
            comma: false,
            hms: false,
            padding: None,
            precision: None,
        }
    }

    /// TODO
    #[inline]
    pub const fn designator(self, designator: Designator) -> SpanPrinter {
        SpanPrinter { designator, ..self }
    }

    /// TODO
    #[inline]
    pub const fn spacing(self, spacing: Spacing) -> SpanPrinter {
        SpanPrinter { spacing, ..self }
    }

    /// TODO
    #[inline]
    pub const fn direction(self, direction: Direction) -> SpanPrinter {
        SpanPrinter { direction, ..self }
    }

    /// TODO
    #[inline]
    pub const fn fractional(
        self,
        unit: Option<FractionalUnit>,
    ) -> SpanPrinter {
        SpanPrinter { fractional: unit, ..self }
    }

    /// TODO
    #[inline]
    pub const fn comma(self, yes: bool) -> SpanPrinter {
        SpanPrinter { comma: yes, ..self }
    }

    /// Formats the span or duration into a `HH:MM:SS[.fffffffff]` format.
    ///
    /// When this is enabled, many of the other options are either ignored or
    /// fixed to a specific setting:
    ///
    /// * Since this format does not use any unit designators, the
    /// [`SpanPrinter::designator`] setting is ignored.
    /// * Since this format uses no whitespace, the [`SpanPrinter::spacing`]
    /// setting is ignored.
    /// * This format does not support a suffix like "ago" to indicate
    /// the sign, so `Direction::Auto` and `Direction::Suffix` are both
    /// equivalent to `Direction::Sign`. That is, a prefix negative sign is
    /// used if the span is negative, otherwise, the sign is omitted. The
    /// `Direction::ForceSign` option is still respected and will emit a `+`
    /// sign for any non-negative span.
    /// * The [`SpanPrinter::fractional`] setting is forcefully set to
    /// [`FractionalUnit::Second`]. It cannot be changed.
    /// * The [`SpanPrinter::comma`] setting is ignored.
    /// * When the padding is not specified, it defaults to `2`.
    /// * The precision setting is respected as documented.
    ///
    /// This format is useful in contexts that are limited to non-calendar
    /// units or for interfacing with existing systems that require this style
    /// of format.
    ///
    /// # Loss of fidelity
    ///
    /// When using this format with a `Span`, sub-second units are formatted
    /// as a fractional second. This means that `1000 milliseconds` and
    /// `1 second` format to precisely the same string. This is similar to the
    /// loss of fidelity when using [`fmt::temporal`](crate::fmt::temporal)
    /// to format spans in the ISO 8601 duration format.
    ///
    /// # Error
    ///
    /// When this setting is enabled, formatting a `Span` with non-zero units
    /// bigger than hours will result in an error.
    ///
    /// # Example
    ///
    /// This shows how to format a `Span` in `HH:MM:SS` format:
    ///
    /// ```
    /// use jiff::{fmt::friendly::SpanPrinter, ToSpan};
    ///
    /// static PRINTER: SpanPrinter =
    ///     SpanPrinter::new().hours_minutes_seconds(true);
    ///
    /// let span = 2.hours().minutes(59).seconds(15).milliseconds(123);
    /// assert_eq!(PRINTER.span_to_string(&span)?, "02:59:15.123");
    /// assert_eq!(PRINTER.span_to_string(&-span)?, "-02:59:15.123");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// And this shows the same, but with a [`SignedDuration`]:
    ///
    /// ```
    /// use jiff::{fmt::friendly::SpanPrinter, SignedDuration};
    ///
    /// static PRINTER: SpanPrinter =
    ///     SpanPrinter::new().hours_minutes_seconds(true);
    ///
    /// let duration = SignedDuration::new(
    ///     2 * 60 * 60 + 59 * 60 + 15,
    ///     123_000_000,
    /// );
    /// assert_eq!(PRINTER.duration_to_string(&duration)?, "02:59:15.123");
    /// assert_eq!(PRINTER.duration_to_string(&-duration)?, "-02:59:15.123");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: `Span` versus `SignedDuration`
    ///
    /// The main advantage of a `Span` is that, except for fractional
    /// components, the unit values emitted correspond precisely to the values
    /// in the `Span`. Where as for a `SignedDuration`, the units are always
    /// computed from a single absolute duration in a way that is always
    /// balanced:
    ///
    /// ```
    /// use jiff::{fmt::friendly::SpanPrinter, SignedDuration, ToSpan};
    ///
    /// static PRINTER: SpanPrinter =
    ///     SpanPrinter::new().hours_minutes_seconds(true);
    ///
    /// let span = 120.minutes();
    /// assert_eq!(PRINTER.span_to_string(&span)?, "00:120:00");
    ///
    /// let duration = SignedDuration::from_mins(120);
    /// assert_eq!(PRINTER.duration_to_string(&duration)?, "02:00:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Of course, a balanced duration is sometimes what you want. But `Span`
    /// affords the flexibility of controlling precisely what the unit values
    /// are.
    #[inline]
    pub const fn hours_minutes_seconds(self, yes: bool) -> SpanPrinter {
        SpanPrinter { hms: yes, ..self }
    }

    /// TODO
    #[inline]
    pub const fn padding(self, digits: u8) -> SpanPrinter {
        SpanPrinter { padding: Some(digits), ..self }
    }

    /// TODO
    #[inline]
    pub const fn precision(self, precision: Option<u8>) -> SpanPrinter {
        SpanPrinter { precision, ..self }
    }

    /// TODO
    pub fn span_to_string(&self, span: &Span) -> Result<String, Error> {
        let mut buf = String::with_capacity(4);
        self.print_span(span, &mut buf)?;
        Ok(buf)
    }

    /// TODO
    pub fn duration_to_string(
        &self,
        duration: &SignedDuration,
    ) -> Result<String, Error> {
        let mut buf = String::with_capacity(4);
        self.print_duration(duration, &mut buf)?;
        Ok(buf)
    }

    /// TODO
    pub fn print_span<W: Write>(
        &self,
        span: &Span,
        wtr: W,
    ) -> Result<(), Error> {
        if self.hms {
            return self.print_span_hms(span, wtr);
        }
        self.print_span_designators(span, wtr)
    }

    /// TODO
    pub fn print_duration<W: Write>(
        &self,
        duration: &SignedDuration,
        wtr: W,
    ) -> Result<(), Error> {
        if self.hms {
            return self.print_duration_hms(duration, wtr);
        }
        self.print_duration_designators(duration, wtr)
    }

    fn print_span_designators<W: Write>(
        &self,
        span: &Span,
        mut wtr: W,
    ) -> Result<(), Error> {
        let mut wtr = DesignatorWriter::new(self, &mut wtr, span.signum());
        wtr.maybe_write_prefix_sign()?;
        match self.fractional {
            None => {
                self.print_span_designators_non_fraction(span, &mut wtr)?;
            }
            Some(unit) => {
                self.print_span_designators_fractional(span, unit, &mut wtr)?;
            }
        }
        wtr.maybe_write_zero()?;
        wtr.maybe_write_suffix_sign()?;
        Ok(())
    }

    fn print_span_designators_non_fraction<'p, 'w, W: Write>(
        &self,
        span: &Span,
        mut wtr: &mut DesignatorWriter<'p, 'w, W>,
    ) -> Result<(), Error> {
        let span = span.abs();
        if span.get_years() != 0 {
            wtr.write(Unit::Year, span.get_years())?;
        }
        if span.get_months() != 0 {
            wtr.write(Unit::Month, span.get_months())?;
        }
        if span.get_weeks() != 0 {
            wtr.write(Unit::Week, span.get_weeks())?;
        }
        if span.get_days() != 0 {
            wtr.write(Unit::Day, span.get_days())?;
        }
        if span.get_hours() != 0 {
            wtr.write(Unit::Hour, span.get_hours())?;
        }
        if span.get_minutes() != 0 {
            wtr.write(Unit::Minute, span.get_minutes())?;
        }
        if span.get_seconds() != 0 {
            wtr.write(Unit::Second, span.get_seconds())?;
        }
        if span.get_milliseconds() != 0 {
            wtr.write(Unit::Millisecond, span.get_milliseconds())?;
        }
        if span.get_microseconds() != 0 {
            wtr.write(Unit::Microsecond, span.get_microseconds())?;
        }
        if span.get_nanoseconds() != 0 {
            wtr.write(Unit::Nanosecond, span.get_nanoseconds())?;
        }
        Ok(())
    }

    #[inline(never)]
    fn print_span_designators_fractional<'p, 'w, W: Write>(
        &self,
        span: &Span,
        unit: FractionalUnit,
        mut wtr: &mut DesignatorWriter<'p, 'w, W>,
    ) -> Result<(), Error> {
        // OK because the biggest FractionalUnit is Hour, and there is always
        // a Unit bigger than hour.
        let split_at = Unit::from(unit).next().unwrap();
        let non_fractional = span.without_lower(split_at);
        let fractional = span.only_lower(split_at);
        self.print_span_designators_non_fraction(&non_fractional, wtr)?;
        wtr.write_fractional_duration(
            unit,
            &fractional.to_jiff_duration_invariant(),
        )?;
        Ok(())
    }

    fn print_span_hms<W: Write>(
        &self,
        span: &Span,
        mut wtr: W,
    ) -> Result<(), Error> {
        if span.largest_unit() > Unit::Hour {
            return Err(err!(
                "using HH:MM:SS friendly duration format with a `Span` \
                 requires that there are no units greater than hours, \
                 but found non-zero units of {plural}",
                plural = span.largest_unit().plural(),
            ));
        }

        let fmtint =
            DecimalFormatter::new().padding(self.padding.unwrap_or(2));
        let fmtfraction = FractionalFormatter::new().precision(self.precision);

        let span = if span.is_negative() {
            wtr.write_str("-")?;
            span.abs()
        } else if let Direction::ForceSign = self.direction {
            wtr.write_str("+")?;
            *span
        } else {
            *span
        };
        wtr.write_int(&fmtint, span.get_hours_ranged().get())?;
        wtr.write_str(":")?;
        wtr.write_int(&fmtint, span.get_minutes_ranged().get())?;
        wtr.write_str(":")?;
        let fp = FractionalPrinter::from_span(
            &span.only_lower(Unit::Minute),
            FractionalUnit::Second,
            fmtint,
            fmtfraction,
        );
        fp.print(&mut wtr)?;
        Ok(())
    }

    fn print_duration_designators<W: Write>(
        &self,
        dur: &SignedDuration,
        mut wtr: W,
    ) -> Result<(), Error> {
        let mut wtr = DesignatorWriter::new(self, &mut wtr, dur.signum());
        wtr.maybe_write_prefix_sign()?;
        match self.fractional {
            None => {
                let mut secs = dur.as_secs();
                wtr.write(Unit::Hour, (secs / SECS_PER_HOUR).abs())?;
                secs %= MINS_PER_HOUR * SECS_PER_MIN;
                wtr.write(Unit::Minute, (secs / SECS_PER_MIN).abs())?;
                wtr.write(Unit::Second, (secs % SECS_PER_MIN).abs())?;
                let mut nanos = dur.subsec_nanos();
                wtr.write(Unit::Millisecond, (nanos / NANOS_PER_MILLI).abs())?;
                nanos %= NANOS_PER_MILLI;
                wtr.write(Unit::Microsecond, (nanos / NANOS_PER_MICRO).abs())?;
                wtr.write(Unit::Nanosecond, nanos % NANOS_PER_MICRO)?;
            }
            Some(FractionalUnit::Hour) => {
                wtr.write_fractional_duration(FractionalUnit::Hour, dur)?;
            }
            Some(FractionalUnit::Minute) => {
                let mut secs = dur.as_secs();
                wtr.write(Unit::Hour, (secs / SECS_PER_HOUR).abs())?;
                secs %= MINS_PER_HOUR * SECS_PER_MIN;

                let leftovers = SignedDuration::new(secs, dur.subsec_nanos());
                wtr.write_fractional_duration(
                    FractionalUnit::Minute,
                    &leftovers,
                )?;
            }
            Some(FractionalUnit::Second) => {
                let mut secs = dur.as_secs();
                wtr.write(Unit::Hour, (secs / SECS_PER_HOUR).abs())?;
                secs %= MINS_PER_HOUR * SECS_PER_MIN;
                wtr.write(Unit::Minute, (secs / SECS_PER_MIN).abs())?;
                secs %= SECS_PER_MIN;

                // Absolute value is OK because -59<=secs<=59 and nanoseconds
                // can never be i32::MIN.
                let leftovers =
                    SignedDuration::new(secs, dur.subsec_nanos()).abs();
                wtr.write_fractional_duration(
                    FractionalUnit::Second,
                    &leftovers,
                )?;
            }
            Some(FractionalUnit::Millisecond) => {
                let mut secs = dur.as_secs();
                wtr.write(Unit::Hour, (secs / SECS_PER_HOUR).abs())?;
                secs %= MINS_PER_HOUR * SECS_PER_MIN;
                wtr.write(Unit::Minute, (secs / SECS_PER_MIN).abs())?;
                wtr.write(Unit::Second, (secs % SECS_PER_MIN).abs())?;

                let leftovers =
                    SignedDuration::new(0, dur.subsec_nanos().abs());
                wtr.write_fractional_duration(
                    FractionalUnit::Millisecond,
                    &leftovers,
                )?;
            }
            Some(FractionalUnit::Microsecond) => {
                let mut secs = dur.as_secs();
                wtr.write(Unit::Hour, (secs / SECS_PER_HOUR).abs())?;
                secs %= MINS_PER_HOUR * SECS_PER_MIN;
                wtr.write(Unit::Minute, (secs / SECS_PER_MIN).abs())?;
                wtr.write(Unit::Second, (secs % SECS_PER_MIN).abs())?;
                let mut nanos = dur.subsec_nanos();
                wtr.write(Unit::Millisecond, (nanos / NANOS_PER_MILLI).abs())?;
                nanos %= NANOS_PER_MILLI;

                let leftovers = SignedDuration::new(0, nanos.abs());
                wtr.write_fractional_duration(
                    FractionalUnit::Microsecond,
                    &leftovers,
                )?;
            }
        }
        wtr.maybe_write_zero()?;
        wtr.maybe_write_suffix_sign()?;
        Ok(())
    }

    fn print_duration_hms<W: Write>(
        &self,
        dur: &SignedDuration,
        mut wtr: W,
    ) -> Result<(), Error> {
        // N.B. It should be technically correct to convert a
        // `SignedDuration` to `Span` (since this process balances)
        // and then format the `Span` as-is. But this doesn't work
        // because the range of a `SignedDuration` is much bigger.

        let fmtint =
            DecimalFormatter::new().padding(self.padding.unwrap_or(2));
        let fmtfraction = FractionalFormatter::new().precision(self.precision);

        if dur.is_negative() {
            wtr.write_str("-")?;
        } else if let Direction::ForceSign = self.direction {
            wtr.write_str("+")?;
        }
        let mut secs = dur.as_secs();
        // OK because guaranteed to be bigger than i64::MIN.
        let hours = (secs / (MINS_PER_HOUR * SECS_PER_MIN)).abs();
        secs %= MINS_PER_HOUR * SECS_PER_MIN;
        // OK because guaranteed to be bigger than i64::MIN.
        let minutes = (secs / SECS_PER_MIN).abs();
        // OK because guaranteed to be bigger than i64::MIN.
        secs = (secs % SECS_PER_MIN).abs();

        wtr.write_int(&fmtint, hours)?;
        wtr.write_str(":")?;
        wtr.write_int(&fmtint, minutes)?;
        wtr.write_str(":")?;
        let fp = FractionalPrinter::from_duration(
            // OK because -999_999_999 <= nanos <= 999_999_999 and secs < 60.
            &SignedDuration::new(secs, dur.subsec_nanos().abs()),
            FractionalUnit::Second,
            fmtint,
            fmtfraction,
        );
        fp.print(&mut wtr)?;
        Ok(())
    }
}

#[derive(Debug)]
struct Designators {
    singular: &'static [&'static str],
    plural: &'static [&'static str],
}

impl Designators {
    const VERBOSE_SINGULAR: &[&str] = &[
        "nanosecond",
        "microsecond",
        "millisecond",
        "second",
        "minute",
        "hour",
        "day",
        "week",
        "month",
        "year",
    ];
    const VERBOSE_PLURAL: &[&str] = &[
        "nanoseconds",
        "microseconds",
        "milliseconds",
        "seconds",
        "minutes",
        "hours",
        "days",
        "weeks",
        "months",
        "years",
    ];

    const SHORT_SINGULAR: &[&str] =
        &["nsec", "µsec", "msec", "sec", "min", "hr", "day", "wk", "mo", "yr"];
    const SHORT_PLURAL: &[&str] = &[
        "nsecs", "µsecs", "msecs", "secs", "mins", "hrs", "days", "wks",
        "mos", "yrs",
    ];

    const COMPACT: &[&str] =
        &["ns", "µs", "ms", "s", "m", "h", "d", "w", "M", "y"];

    fn new(config: Designator) -> Designators {
        match config {
            Designator::Verbose => Designators {
                singular: Designators::VERBOSE_SINGULAR,
                plural: Designators::VERBOSE_PLURAL,
            },
            Designator::Short => Designators {
                singular: Designators::SHORT_SINGULAR,
                plural: Designators::SHORT_PLURAL,
            },
            Designator::Compact => Designators {
                singular: Designators::COMPACT,
                plural: Designators::COMPACT,
            },
        }
    }

    fn designator(&self, unit: impl Into<Unit>, plural: bool) -> &'static str {
        let unit = unit.into();
        let index = unit as usize;
        if plural {
            self.plural[index]
        } else {
            self.singular[index]
        }
    }
}

/// An abstraction for writing the "designator" variant of the friendly format.
///
/// This takes care of computing some initial state and keeping track of some
/// mutable state that influences printing. For example, whether to write a
/// delimiter or not (one should only come after a unit that has been written).
#[derive(Debug)]
struct DesignatorWriter<'p, 'w, W> {
    printer: &'p SpanPrinter,
    wtr: &'w mut W,
    desig: Designators,
    sign: Option<DirectionSign>,
    fmtint: DecimalFormatter,
    fmtfraction: FractionalFormatter,
    written_non_zero_unit: bool,
}

impl<'p, 'w, W: Write> DesignatorWriter<'p, 'w, W> {
    fn new(
        printer: &'p SpanPrinter,
        wtr: &'w mut W,
        signum: i8,
    ) -> DesignatorWriter<'p, 'w, W> {
        let desig = Designators::new(printer.designator);
        let sign = printer.direction.sign(printer.spacing, signum);
        let fmtint =
            DecimalFormatter::new().padding(printer.padding.unwrap_or(0));
        let fmtfraction =
            FractionalFormatter::new().precision(printer.precision);
        DesignatorWriter {
            printer,
            wtr,
            desig,
            sign,
            fmtint,
            fmtfraction,
            written_non_zero_unit: false,
        }
    }

    fn maybe_write_prefix_sign(&mut self) -> Result<(), Error> {
        if let Some(DirectionSign::Prefix(sign)) = self.sign {
            self.wtr.write_str(sign)?;
        }
        Ok(())
    }

    fn maybe_write_suffix_sign(&mut self) -> Result<(), Error> {
        if let Some(DirectionSign::Suffix(sign)) = self.sign {
            self.wtr.write_str(sign)?;
        }
        Ok(())
    }

    fn maybe_write_zero(&mut self) -> Result<(), Error> {
        if self.written_non_zero_unit {
            return Ok(());
        }
        // If a fractional unit is set, then we should use that unit
        // specifically to express "zero."
        let unit =
            self.printer.fractional.map(Unit::from).unwrap_or(Unit::Second);
        self.wtr.write_int(&self.fmtint, 0)?;
        self.wtr
            .write_str(self.printer.spacing.between_value_and_designator())?;
        self.wtr.write_str(self.desig.designator(unit, true))?;
        Ok(())
    }

    fn write(
        &mut self,
        unit: Unit,
        value: impl Into<i64>,
    ) -> Result<(), Error> {
        let value = value.into();
        if value == 0 {
            return Ok(());
        }
        self.finish_preceding()?;
        self.written_non_zero_unit = true;
        self.wtr.write_int(&self.fmtint, value)?;
        self.wtr
            .write_str(self.printer.spacing.between_value_and_designator())?;
        self.wtr.write_str(self.desig.designator(unit, value != 1))?;
        Ok(())
    }

    fn write_fractional_duration(
        &mut self,
        unit: FractionalUnit,
        duration: &SignedDuration,
    ) -> Result<(), Error> {
        let fp = FractionalPrinter::from_duration(
            duration,
            unit,
            self.fmtint,
            self.fmtfraction,
        );
        if !fp.must_write_digits() {
            return Ok(());
        }
        self.finish_preceding()?;
        self.written_non_zero_unit = true;
        fp.print(&mut *self.wtr)?;
        self.wtr
            .write_str(self.printer.spacing.between_value_and_designator())?;
        self.wtr.write_str(self.desig.designator(unit, fp.is_plural()))?;
        Ok(())
    }

    fn finish_preceding(&mut self) -> Result<(), Error> {
        if self.written_non_zero_unit {
            if self.printer.comma {
                self.wtr.write_str(",")?;
            }
            self.wtr.write_str(self.printer.spacing.between_units())?;
        }
        Ok(())
    }
}

struct FractionalPrinter {
    integer: i64,
    fraction: i64,
    fmtint: DecimalFormatter,
    fmtfraction: FractionalFormatter,
}

impl FractionalPrinter {
    /// Build a fractional printer for the `Span` given. This includes the `.`.
    ///
    /// Callers must ensure that all units greater than `FractionalUnit` are
    /// zero in the span given.
    ///
    /// Note that the printer returned only prints a fractional component
    /// if necessary. For example, if the fractional component is zero and
    /// precision is `None`, or if `precision` is `Some(0)`, then no fractional
    /// component will be emitted.
    fn from_span(
        span: &Span,
        unit: FractionalUnit,
        fmtint: DecimalFormatter,
        fmtfraction: FractionalFormatter,
    ) -> FractionalPrinter {
        debug_assert!(span.largest_unit() <= Unit::from(unit));
        let dur = span.to_jiff_duration_invariant();
        FractionalPrinter::from_duration(&dur, unit, fmtint, fmtfraction)
    }

    /// Like `from_span`, but for `SignedDuration`.
    fn from_duration(
        dur: &SignedDuration,
        unit: FractionalUnit,
        fmtint: DecimalFormatter,
        fmtfraction: FractionalFormatter,
    ) -> FractionalPrinter {
        // Should we assume `dur` is non-negative in this context?
        // I don't think we can in general, because `dur` could
        // be `SignedDuration::MIN` in the case where `unit` is
        // `FractionalUnit::Hour`. In this case, the caller can't call `abs`
        // because it would panic.
        match unit {
            FractionalUnit::Hour => {
                let integer = (dur.as_secs() / SECS_PER_HOUR).abs();
                let fraction = dur.as_nanos() % NANOS_PER_HOUR;
                // OK because NANOS_PER_HOUR fits in an i64.
                debug_assert!(fraction <= i128::from(i64::MAX));
                let mut fraction = i64::try_from(fraction).unwrap();
                // Drop precision since we're only allowed 9 decimal places.
                fraction /= SECS_PER_HOUR;
                // OK because fraction can't be i64::MIN.
                fraction = fraction.abs();
                FractionalPrinter { integer, fraction, fmtint, fmtfraction }
            }
            FractionalUnit::Minute => {
                let integer = (dur.as_secs() / SECS_PER_MIN).abs();
                let fraction = dur.as_nanos() % NANOS_PER_MIN;
                // OK because NANOS_PER_HOUR fits in an i64.
                debug_assert!(fraction <= i128::from(i64::MAX));
                let mut fraction = i64::try_from(fraction).unwrap();
                // Drop precision since we're only allowed 9 decimal places.
                fraction /= SECS_PER_MIN;
                // OK because fraction can't be i64::MIN.
                fraction = fraction.abs();
                FractionalPrinter { integer, fraction, fmtint, fmtfraction }
            }
            FractionalUnit::Second => {
                let integer = dur.as_secs();
                let fraction = i64::from(dur.subsec_nanos());
                FractionalPrinter { integer, fraction, fmtint, fmtfraction }
            }
            FractionalUnit::Millisecond => {
                // Unwrap is OK, but this is subtle. For printing a
                // SignedDuration, as_millis() can never return anything
                // bigger than 1 second. So that case is clearly okay. But
                // for printing a Span, it can, since spans can be totally
                // unbalanced. But Spans have limits on their units such that
                // each will fit into an i64. So this is also okay in that case
                // too.
                let integer = i64::try_from(dur.as_millis()).unwrap();
                let fraction =
                    i64::from((dur.subsec_nanos() % NANOS_PER_MILLI) * 1_000);
                FractionalPrinter { integer, fraction, fmtint, fmtfraction }
            }
            FractionalUnit::Microsecond => {
                // Unwrap is OK, but this is subtle. For printing a
                // SignedDuration, as_micros() can never return anything
                // bigger than 1 millisecond. So that case is clearly okay. But
                // for printing a Span, it can, since spans can be totally
                // unbalanced. But Spans have limits on their units such that
                // each will fit into an i64. So this is also okay in that case
                // too.
                let integer = i64::try_from(dur.as_micros()).unwrap();
                let fraction = i64::from(
                    (dur.subsec_nanos() % NANOS_PER_MICRO) * 1_000_000,
                );
                FractionalPrinter { integer, fraction, fmtint, fmtfraction }
            }
        }
    }

    /// Returns true if both the integer and fractional component are zero.
    fn is_zero(&self) -> bool {
        self.integer == 0 && self.fraction == 0
    }

    /// Returns true if this integer/fraction should be considered plural
    /// when choosing what designator to use.
    fn is_plural(&self) -> bool {
        self.integer != 1
            || (self.fraction != 0
                && !self.fmtfraction.has_zero_fixed_precision())
    }

    /// Returns true if and only if this printer must write some kind of number
    /// when `print` is called.
    ///
    /// The only case where this returns `false` is when both the integer and
    /// fractional component are zero *and* the precision is fixed to a number
    /// greater than zero.
    fn must_write_digits(&self) -> bool {
        !self.is_zero() || self.fmtfraction.has_non_zero_fixed_precision()
    }

    /// Prints the integer and optional fractional component.
    ///
    /// This will always print the integer, even if it's zero. Therefore, if
    /// the caller wants to omit printing zero, the caller should do their own
    /// conditional logic.
    fn print<W: Write>(&self, mut wtr: W) -> Result<(), Error> {
        wtr.write_int(&self.fmtint, self.integer)?;
        if self.fmtfraction.will_write_digits(self.fraction) {
            wtr.write_str(".")?;
            wtr.write_fraction(&self.fmtfraction, self.fraction)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ToSpan;

    use super::*;

    #[test]
    fn print_span_designator_default() {
        let printer = || SpanPrinter::new();
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"1sec");
        insta::assert_snapshot!(p(2.seconds()), @"2secs");
        insta::assert_snapshot!(p(10.seconds()), @"10secs");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"1min 40secs");

        insta::assert_snapshot!(p(1.minute()), @"1min");
        insta::assert_snapshot!(p(2.minutes()), @"2mins");
        insta::assert_snapshot!(p(10.minutes()), @"10mins");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"1hr 40mins");

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(p(2.hours()), @"2hrs");
        insta::assert_snapshot!(p(10.hours()), @"10hrs");
        insta::assert_snapshot!(p(100.hours()), @"100hrs");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"1hr 1min 1sec",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"2hrs 2mins 2secs",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100hrs 100mins 100secs",
        );

        insta::assert_snapshot!(p(-1.hour()), @"1hr ago");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"1hr 30secs ago");
    }

    #[test]
    fn print_span_designator_verbose() {
        let printer = || SpanPrinter::new().designator(Designator::Verbose);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"1second");
        insta::assert_snapshot!(p(2.seconds()), @"2seconds");
        insta::assert_snapshot!(p(10.seconds()), @"10seconds");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"1minute 40seconds");

        insta::assert_snapshot!(p(1.minute()), @"1minute");
        insta::assert_snapshot!(p(2.minutes()), @"2minutes");
        insta::assert_snapshot!(p(10.minutes()), @"10minutes");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"1hour 40minutes");

        insta::assert_snapshot!(p(1.hour()), @"1hour");
        insta::assert_snapshot!(p(2.hours()), @"2hours");
        insta::assert_snapshot!(p(10.hours()), @"10hours");
        insta::assert_snapshot!(p(100.hours()), @"100hours");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"1hour 1minute 1second",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"2hours 2minutes 2seconds",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10hours 10minutes 10seconds",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100hours 100minutes 100seconds",
        );

        insta::assert_snapshot!(p(-1.hour()), @"1hour ago");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"1hour 30seconds ago");
    }

    #[test]
    fn print_span_designator_short() {
        let printer = || SpanPrinter::new().designator(Designator::Short);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"1sec");
        insta::assert_snapshot!(p(2.seconds()), @"2secs");
        insta::assert_snapshot!(p(10.seconds()), @"10secs");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"1min 40secs");

        insta::assert_snapshot!(p(1.minute()), @"1min");
        insta::assert_snapshot!(p(2.minutes()), @"2mins");
        insta::assert_snapshot!(p(10.minutes()), @"10mins");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"1hr 40mins");

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(p(2.hours()), @"2hrs");
        insta::assert_snapshot!(p(10.hours()), @"10hrs");
        insta::assert_snapshot!(p(100.hours()), @"100hrs");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"1hr 1min 1sec",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"2hrs 2mins 2secs",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100hrs 100mins 100secs",
        );

        insta::assert_snapshot!(p(-1.hour()), @"1hr ago");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"1hr 30secs ago");
    }

    #[test]
    fn print_span_designator_compact() {
        let printer = || SpanPrinter::new().designator(Designator::Compact);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"1s");
        insta::assert_snapshot!(p(2.seconds()), @"2s");
        insta::assert_snapshot!(p(10.seconds()), @"10s");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"1m 40s");

        insta::assert_snapshot!(p(1.minute()), @"1m");
        insta::assert_snapshot!(p(2.minutes()), @"2m");
        insta::assert_snapshot!(p(10.minutes()), @"10m");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"1h 40m");

        insta::assert_snapshot!(p(1.hour()), @"1h");
        insta::assert_snapshot!(p(2.hours()), @"2h");
        insta::assert_snapshot!(p(10.hours()), @"10h");
        insta::assert_snapshot!(p(100.hours()), @"100h");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"1h 1m 1s",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"2h 2m 2s",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10h 10m 10s",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100h 100m 100s",
        );

        insta::assert_snapshot!(p(-1.hour()), @"1h ago");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"1h 30s ago");
    }

    #[test]
    fn print_span_designator_direction_force() {
        let printer = || SpanPrinter::new().direction(Direction::ForceSign);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"+1sec");
        insta::assert_snapshot!(p(2.seconds()), @"+2secs");
        insta::assert_snapshot!(p(10.seconds()), @"+10secs");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"+1min 40secs");

        insta::assert_snapshot!(p(1.minute()), @"+1min");
        insta::assert_snapshot!(p(2.minutes()), @"+2mins");
        insta::assert_snapshot!(p(10.minutes()), @"+10mins");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"+1hr 40mins");

        insta::assert_snapshot!(p(1.hour()), @"+1hr");
        insta::assert_snapshot!(p(2.hours()), @"+2hrs");
        insta::assert_snapshot!(p(10.hours()), @"+10hrs");
        insta::assert_snapshot!(p(100.hours()), @"+100hrs");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"+1hr 1min 1sec",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"+2hrs 2mins 2secs",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"+10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"+100hrs 100mins 100secs",
        );

        insta::assert_snapshot!(p(-1.hour()), @"-1hr");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"-1hr 30secs");
    }

    #[test]
    fn print_span_designator_padding() {
        let printer = || SpanPrinter::new().padding(2);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"01sec");
        insta::assert_snapshot!(p(2.seconds()), @"02secs");
        insta::assert_snapshot!(p(10.seconds()), @"10secs");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"01min 40secs");

        insta::assert_snapshot!(p(1.minute()), @"01min");
        insta::assert_snapshot!(p(2.minutes()), @"02mins");
        insta::assert_snapshot!(p(10.minutes()), @"10mins");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"01hr 40mins");

        insta::assert_snapshot!(p(1.hour()), @"01hr");
        insta::assert_snapshot!(p(2.hours()), @"02hrs");
        insta::assert_snapshot!(p(10.hours()), @"10hrs");
        insta::assert_snapshot!(p(100.hours()), @"100hrs");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"01hr 01min 01sec",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"02hrs 02mins 02secs",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100hrs 100mins 100secs",
        );

        insta::assert_snapshot!(p(-1.hour()), @"01hr ago");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"01hr 30secs ago");
    }

    #[test]
    fn print_span_designator_spacing_none() {
        let printer = || SpanPrinter::new().spacing(Spacing::None);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"1sec");
        insta::assert_snapshot!(p(2.seconds()), @"2secs");
        insta::assert_snapshot!(p(10.seconds()), @"10secs");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"1min40secs");

        insta::assert_snapshot!(p(1.minute()), @"1min");
        insta::assert_snapshot!(p(2.minutes()), @"2mins");
        insta::assert_snapshot!(p(10.minutes()), @"10mins");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"1hr40mins");

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(p(2.hours()), @"2hrs");
        insta::assert_snapshot!(p(10.hours()), @"10hrs");
        insta::assert_snapshot!(p(100.hours()), @"100hrs");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"1hr1min1sec",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"2hrs2mins2secs",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10hrs10mins10secs",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100hrs100mins100secs",
        );

        insta::assert_snapshot!(p(-1.hour()), @"-1hr");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"-1hr30secs");
    }

    #[test]
    fn print_span_designator_spacing_more() {
        let printer =
            || SpanPrinter::new().spacing(Spacing::BetweenUnitsAndDesignators);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"1 sec");
        insta::assert_snapshot!(p(2.seconds()), @"2 secs");
        insta::assert_snapshot!(p(10.seconds()), @"10 secs");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"1 min 40 secs");

        insta::assert_snapshot!(p(1.minute()), @"1 min");
        insta::assert_snapshot!(p(2.minutes()), @"2 mins");
        insta::assert_snapshot!(p(10.minutes()), @"10 mins");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"1 hr 40 mins");

        insta::assert_snapshot!(p(1.hour()), @"1 hr");
        insta::assert_snapshot!(p(2.hours()), @"2 hrs");
        insta::assert_snapshot!(p(10.hours()), @"10 hrs");
        insta::assert_snapshot!(p(100.hours()), @"100 hrs");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"1 hr 1 min 1 sec",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"2 hrs 2 mins 2 secs",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10 hrs 10 mins 10 secs",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100 hrs 100 mins 100 secs",
        );

        insta::assert_snapshot!(p(-1.hour()), @"1 hr ago");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"1 hr 30 secs ago");
    }

    #[test]
    fn print_span_designator_spacing_comma() {
        let printer = || {
            SpanPrinter::new()
                .comma(true)
                .spacing(Spacing::BetweenUnitsAndDesignators)
        };
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"1 sec");
        insta::assert_snapshot!(p(2.seconds()), @"2 secs");
        insta::assert_snapshot!(p(10.seconds()), @"10 secs");
        insta::assert_snapshot!(p(1.minute().seconds(40)), @"1 min, 40 secs");

        insta::assert_snapshot!(p(1.minute()), @"1 min");
        insta::assert_snapshot!(p(2.minutes()), @"2 mins");
        insta::assert_snapshot!(p(10.minutes()), @"10 mins");
        insta::assert_snapshot!(p(1.hour().minutes(40)), @"1 hr, 40 mins");

        insta::assert_snapshot!(p(1.hour()), @"1 hr");
        insta::assert_snapshot!(p(2.hours()), @"2 hrs");
        insta::assert_snapshot!(p(10.hours()), @"10 hrs");
        insta::assert_snapshot!(p(100.hours()), @"100 hrs");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"1 hr, 1 min, 1 sec",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"2 hrs, 2 mins, 2 secs",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10 hrs, 10 mins, 10 secs",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100 hrs, 100 mins, 100 secs",
        );

        insta::assert_snapshot!(p(-1.hour()), @"1 hr ago");
        insta::assert_snapshot!(p(-1.hour().seconds(30)), @"1 hr, 30 secs ago");
    }

    #[test]
    fn print_span_designator_fractional_hour() {
        let printer =
            || SpanPrinter::new().fractional(Some(FractionalUnit::Hour));
        let p = |span| printer().span_to_string(&span).unwrap();
        let pp = |precision, span| {
            printer().precision(Some(precision)).span_to_string(&span).unwrap()
        };

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(pp(0, 1.hour()), @"1hr");
        insta::assert_snapshot!(pp(1, 1.hour()), @"1.0hr");
        insta::assert_snapshot!(pp(2, 1.hour()), @"1.00hr");

        insta::assert_snapshot!(p(1.hour().minutes(30)), @"1.5hrs");
        insta::assert_snapshot!(pp(0, 1.hour().minutes(30)), @"1hr");
        insta::assert_snapshot!(pp(1, 1.hour().minutes(30)), @"1.5hrs");
        insta::assert_snapshot!(pp(2, 1.hour().minutes(30)), @"1.50hrs");

        insta::assert_snapshot!(p(1.hour().minutes(3)), @"1.05hrs");
        insta::assert_snapshot!(p(1.hour().minutes(3).nanoseconds(1)), @"1.05hrs");
        insta::assert_snapshot!(p(1.second()), @"0.000277777hrs");
        // precision loss!
        insta::assert_snapshot!(p(1.second().nanoseconds(1)), @"0.000277777hrs");
        insta::assert_snapshot!(p(0.seconds()), @"0hrs");
        // precision loss!
        insta::assert_snapshot!(p(1.nanosecond()), @"0hrs");
    }

    #[test]
    fn print_span_designator_fractional_minute() {
        let printer =
            || SpanPrinter::new().fractional(Some(FractionalUnit::Minute));
        let p = |span| printer().span_to_string(&span).unwrap();
        let pp = |precision, span| {
            printer().precision(Some(precision)).span_to_string(&span).unwrap()
        };

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(p(1.hour().minutes(30)), @"1hr 30mins");

        insta::assert_snapshot!(p(1.minute()), @"1min");
        insta::assert_snapshot!(pp(0, 1.minute()), @"1min");
        insta::assert_snapshot!(pp(1, 1.minute()), @"1.0min");
        insta::assert_snapshot!(pp(2, 1.minute()), @"1.00min");

        insta::assert_snapshot!(p(1.minute().seconds(30)), @"1.5mins");
        insta::assert_snapshot!(pp(0, 1.minute().seconds(30)), @"1min");
        insta::assert_snapshot!(pp(1, 1.minute().seconds(30)), @"1.5mins");
        insta::assert_snapshot!(pp(2, 1.minute().seconds(30)), @"1.50mins");

        insta::assert_snapshot!(p(1.hour().nanoseconds(1)), @"1hr");
        insta::assert_snapshot!(p(1.minute().seconds(3)), @"1.05mins");
        insta::assert_snapshot!(p(1.minute().seconds(3).nanoseconds(1)), @"1.05mins");
        insta::assert_snapshot!(p(1.second()), @"0.016666666mins");
        // precision loss!
        insta::assert_snapshot!(p(1.second().nanoseconds(1)), @"0.016666666mins");
        insta::assert_snapshot!(p(0.seconds()), @"0mins");
        // precision loss!
        insta::assert_snapshot!(p(1.nanosecond()), @"0mins");
    }

    #[test]
    fn print_span_designator_fractional_second() {
        let printer =
            || SpanPrinter::new().fractional(Some(FractionalUnit::Second));
        let p = |span| printer().span_to_string(&span).unwrap();
        let pp = |precision, span| {
            printer().precision(Some(precision)).span_to_string(&span).unwrap()
        };

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(p(1.hour().minutes(30)), @"1hr 30mins");

        insta::assert_snapshot!(p(1.second()), @"1sec");
        insta::assert_snapshot!(pp(0, 1.second()), @"1sec");
        insta::assert_snapshot!(pp(1, 1.second()), @"1.0sec");
        insta::assert_snapshot!(pp(2, 1.second()), @"1.00sec");

        insta::assert_snapshot!(p(1.second().milliseconds(500)), @"1.5secs");
        insta::assert_snapshot!(pp(0, 1.second().milliseconds(500)), @"1sec");
        insta::assert_snapshot!(pp(1, 1.second().milliseconds(500)), @"1.5secs");
        insta::assert_snapshot!(pp(2, 1.second().milliseconds(500)), @"1.50secs");

        insta::assert_snapshot!(p(1.second().nanoseconds(1)), @"1.000000001secs");
        insta::assert_snapshot!(p(1.nanosecond()), @"0.000000001secs");
        insta::assert_snapshot!(p(0.seconds()), @"0secs");
    }

    #[test]
    fn print_span_designator_fractional_millisecond() {
        let printer = || {
            SpanPrinter::new().fractional(Some(FractionalUnit::Millisecond))
        };
        let p = |span| printer().span_to_string(&span).unwrap();
        let pp = |precision, span| {
            printer().precision(Some(precision)).span_to_string(&span).unwrap()
        };

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(p(1.hour().minutes(30)), @"1hr 30mins");
        insta::assert_snapshot!(
            p(1.hour().minutes(30).seconds(10)),
            @"1hr 30mins 10secs",
        );

        insta::assert_snapshot!(p(1.second()), @"1sec");
        insta::assert_snapshot!(pp(0, 1.second()), @"1sec");
        insta::assert_snapshot!(pp(1, 1.second()), @"1sec 0.0msecs");
        insta::assert_snapshot!(pp(2, 1.second()), @"1sec 0.00msecs");

        insta::assert_snapshot!(p(1.second().milliseconds(500)), @"1sec 500msecs");
        insta::assert_snapshot!(
            pp(0, 1.second().milliseconds(1).microseconds(500)),
            @"1sec 1msec",
        );
        insta::assert_snapshot!(
            pp(1, 1.second().milliseconds(1).microseconds(500)),
            @"1sec 1.5msecs",
        );
        insta::assert_snapshot!(
            pp(2, 1.second().milliseconds(1).microseconds(500)),
            @"1sec 1.50msecs",
        );

        insta::assert_snapshot!(p(1.millisecond().nanoseconds(1)), @"1.000001msecs");
        insta::assert_snapshot!(p(1.nanosecond()), @"0.000001msecs");
        insta::assert_snapshot!(p(0.seconds()), @"0msecs");
    }

    #[test]
    fn print_span_designator_fractional_microsecond() {
        let printer = || {
            SpanPrinter::new().fractional(Some(FractionalUnit::Microsecond))
        };
        let p = |span| printer().span_to_string(&span).unwrap();
        let pp = |precision, span| {
            printer().precision(Some(precision)).span_to_string(&span).unwrap()
        };

        insta::assert_snapshot!(p(1.hour()), @"1hr");
        insta::assert_snapshot!(p(1.hour().minutes(30)), @"1hr 30mins");
        insta::assert_snapshot!(
            p(1.hour().minutes(30).seconds(10)),
            @"1hr 30mins 10secs",
        );

        insta::assert_snapshot!(p(1.second()), @"1sec");
        insta::assert_snapshot!(pp(0, 1.second()), @"1sec");
        insta::assert_snapshot!(pp(1, 1.second()), @"1sec 0.0µsecs");
        insta::assert_snapshot!(pp(2, 1.second()), @"1sec 0.00µsecs");

        insta::assert_snapshot!(p(1.second().milliseconds(500)), @"1sec 500msecs");
        insta::assert_snapshot!(
            pp(0, 1.second().milliseconds(1).microseconds(500)),
            @"1sec 1msec 500µsecs",
        );
        insta::assert_snapshot!(
            pp(1, 1.second().milliseconds(1).microseconds(500)),
            @"1sec 1msec 500.0µsecs",
        );
        insta::assert_snapshot!(
            pp(2, 1.second().milliseconds(1).microseconds(500)),
            @"1sec 1msec 500.00µsecs",
        );

        insta::assert_snapshot!(
            p(1.millisecond().nanoseconds(1)),
            @"1msec 0.001µsecs",
        );
        insta::assert_snapshot!(p(1.nanosecond()), @"0.001µsecs");
        insta::assert_snapshot!(p(0.second()), @"0µsecs");
    }

    #[test]
    fn print_duration_designator_default() {
        let printer = || SpanPrinter::new();
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"1sec");
        insta::assert_snapshot!(p(2), @"2secs");
        insta::assert_snapshot!(p(10), @"10secs");
        insta::assert_snapshot!(p(100), @"1min 40secs");

        insta::assert_snapshot!(p(1 * 60), @"1min");
        insta::assert_snapshot!(p(2 * 60), @"2mins");
        insta::assert_snapshot!(p(10 * 60), @"10mins");
        insta::assert_snapshot!(p(100 * 60), @"1hr 40mins");

        insta::assert_snapshot!(p(1 * 60 * 60), @"1hr");
        insta::assert_snapshot!(p(2 * 60 * 60), @"2hrs");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10hrs");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100hrs");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"1hr 1min 1sec",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"2hrs 2mins 2secs",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101hrs 41mins 40secs",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"1hr ago");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"1hr 30secs ago");
    }

    #[test]
    fn print_duration_designator_verbose() {
        let printer = || SpanPrinter::new().designator(Designator::Verbose);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"1second");
        insta::assert_snapshot!(p(2), @"2seconds");
        insta::assert_snapshot!(p(10), @"10seconds");
        insta::assert_snapshot!(p(100), @"1minute 40seconds");

        insta::assert_snapshot!(p(1 * 60), @"1minute");
        insta::assert_snapshot!(p(2 * 60), @"2minutes");
        insta::assert_snapshot!(p(10 * 60), @"10minutes");
        insta::assert_snapshot!(p(100 * 60), @"1hour 40minutes");

        insta::assert_snapshot!(p(1 * 60 * 60), @"1hour");
        insta::assert_snapshot!(p(2 * 60 * 60), @"2hours");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10hours");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100hours");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"1hour 1minute 1second",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"2hours 2minutes 2seconds",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10hours 10minutes 10seconds",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101hours 41minutes 40seconds",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"1hour ago");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"1hour 30seconds ago");
    }

    #[test]
    fn print_duration_designator_short() {
        let printer = || SpanPrinter::new().designator(Designator::Short);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"1sec");
        insta::assert_snapshot!(p(2), @"2secs");
        insta::assert_snapshot!(p(10), @"10secs");
        insta::assert_snapshot!(p(100), @"1min 40secs");

        insta::assert_snapshot!(p(1 * 60), @"1min");
        insta::assert_snapshot!(p(2 * 60), @"2mins");
        insta::assert_snapshot!(p(10 * 60), @"10mins");
        insta::assert_snapshot!(p(100 * 60), @"1hr 40mins");

        insta::assert_snapshot!(p(1 * 60 * 60), @"1hr");
        insta::assert_snapshot!(p(2 * 60 * 60), @"2hrs");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10hrs");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100hrs");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"1hr 1min 1sec",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"2hrs 2mins 2secs",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101hrs 41mins 40secs",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"1hr ago");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"1hr 30secs ago");
    }

    #[test]
    fn print_duration_designator_compact() {
        let printer = || SpanPrinter::new().designator(Designator::Compact);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"1s");
        insta::assert_snapshot!(p(2), @"2s");
        insta::assert_snapshot!(p(10), @"10s");
        insta::assert_snapshot!(p(100), @"1m 40s");

        insta::assert_snapshot!(p(1 * 60), @"1m");
        insta::assert_snapshot!(p(2 * 60), @"2m");
        insta::assert_snapshot!(p(10 * 60), @"10m");
        insta::assert_snapshot!(p(100 * 60), @"1h 40m");

        insta::assert_snapshot!(p(1 * 60 * 60), @"1h");
        insta::assert_snapshot!(p(2 * 60 * 60), @"2h");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10h");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100h");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"1h 1m 1s",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"2h 2m 2s",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10h 10m 10s",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101h 41m 40s",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"1h ago");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"1h 30s ago");
    }

    #[test]
    fn print_duration_designator_direction_force() {
        let printer = || SpanPrinter::new().direction(Direction::ForceSign);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"+1sec");
        insta::assert_snapshot!(p(2), @"+2secs");
        insta::assert_snapshot!(p(10), @"+10secs");
        insta::assert_snapshot!(p(100), @"+1min 40secs");

        insta::assert_snapshot!(p(1 * 60), @"+1min");
        insta::assert_snapshot!(p(2 * 60), @"+2mins");
        insta::assert_snapshot!(p(10 * 60), @"+10mins");
        insta::assert_snapshot!(p(100 * 60), @"+1hr 40mins");

        insta::assert_snapshot!(p(1 * 60 * 60), @"+1hr");
        insta::assert_snapshot!(p(2 * 60 * 60), @"+2hrs");
        insta::assert_snapshot!(p(10 * 60 * 60), @"+10hrs");
        insta::assert_snapshot!(p(100 * 60 * 60), @"+100hrs");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"+1hr 1min 1sec",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"+2hrs 2mins 2secs",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"+10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"+101hrs 41mins 40secs",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"-1hr");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"-1hr 30secs");
    }

    #[test]
    fn print_duration_designator_padding() {
        let printer = || SpanPrinter::new().padding(2);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"01sec");
        insta::assert_snapshot!(p(2), @"02secs");
        insta::assert_snapshot!(p(10), @"10secs");
        insta::assert_snapshot!(p(100), @"01min 40secs");

        insta::assert_snapshot!(p(1 * 60), @"01min");
        insta::assert_snapshot!(p(2 * 60), @"02mins");
        insta::assert_snapshot!(p(10 * 60), @"10mins");
        insta::assert_snapshot!(p(100 * 60), @"01hr 40mins");

        insta::assert_snapshot!(p(1 * 60 * 60), @"01hr");
        insta::assert_snapshot!(p(2 * 60 * 60), @"02hrs");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10hrs");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100hrs");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"01hr 01min 01sec",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"02hrs 02mins 02secs",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10hrs 10mins 10secs",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101hrs 41mins 40secs",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"01hr ago");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"01hr 30secs ago");
    }

    #[test]
    fn print_duration_designator_spacing_none() {
        let printer = || SpanPrinter::new().spacing(Spacing::None);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"1sec");
        insta::assert_snapshot!(p(2), @"2secs");
        insta::assert_snapshot!(p(10), @"10secs");
        insta::assert_snapshot!(p(100), @"1min40secs");

        insta::assert_snapshot!(p(1 * 60), @"1min");
        insta::assert_snapshot!(p(2 * 60), @"2mins");
        insta::assert_snapshot!(p(10 * 60), @"10mins");
        insta::assert_snapshot!(p(100 * 60), @"1hr40mins");

        insta::assert_snapshot!(p(1 * 60 * 60), @"1hr");
        insta::assert_snapshot!(p(2 * 60 * 60), @"2hrs");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10hrs");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100hrs");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"1hr1min1sec",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"2hrs2mins2secs",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10hrs10mins10secs",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101hrs41mins40secs",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"-1hr");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"-1hr30secs");
    }

    #[test]
    fn print_duration_designator_spacing_more() {
        let printer =
            || SpanPrinter::new().spacing(Spacing::BetweenUnitsAndDesignators);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"1 sec");
        insta::assert_snapshot!(p(2), @"2 secs");
        insta::assert_snapshot!(p(10), @"10 secs");
        insta::assert_snapshot!(p(100), @"1 min 40 secs");

        insta::assert_snapshot!(p(1 * 60), @"1 min");
        insta::assert_snapshot!(p(2 * 60), @"2 mins");
        insta::assert_snapshot!(p(10 * 60), @"10 mins");
        insta::assert_snapshot!(p(100 * 60), @"1 hr 40 mins");

        insta::assert_snapshot!(p(1 * 60 * 60), @"1 hr");
        insta::assert_snapshot!(p(2 * 60 * 60), @"2 hrs");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10 hrs");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100 hrs");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"1 hr 1 min 1 sec",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"2 hrs 2 mins 2 secs",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10 hrs 10 mins 10 secs",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101 hrs 41 mins 40 secs",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"1 hr ago");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"1 hr 30 secs ago");
    }

    #[test]
    fn print_duration_designator_spacing_comma() {
        let printer = || {
            SpanPrinter::new()
                .comma(true)
                .spacing(Spacing::BetweenUnitsAndDesignators)
        };
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        insta::assert_snapshot!(p(1), @"1 sec");
        insta::assert_snapshot!(p(2), @"2 secs");
        insta::assert_snapshot!(p(10), @"10 secs");
        insta::assert_snapshot!(p(100), @"1 min, 40 secs");

        insta::assert_snapshot!(p(1 * 60), @"1 min");
        insta::assert_snapshot!(p(2 * 60), @"2 mins");
        insta::assert_snapshot!(p(10 * 60), @"10 mins");
        insta::assert_snapshot!(p(100 * 60), @"1 hr, 40 mins");

        insta::assert_snapshot!(p(1 * 60 * 60), @"1 hr");
        insta::assert_snapshot!(p(2 * 60 * 60), @"2 hrs");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10 hrs");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100 hrs");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"1 hr, 1 min, 1 sec",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"2 hrs, 2 mins, 2 secs",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10 hrs, 10 mins, 10 secs",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101 hrs, 41 mins, 40 secs",
        );

        insta::assert_snapshot!(p(-1 * 60 * 60), @"1 hr ago");
        insta::assert_snapshot!(p(-1 * 60 * 60 - 30), @"1 hr, 30 secs ago");
    }

    #[test]
    fn print_duration_designator_fractional_hour() {
        let printer =
            || SpanPrinter::new().fractional(Some(FractionalUnit::Hour));
        let p = |secs, nanos| {
            printer()
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };
        let pp = |precision, secs, nanos| {
            printer()
                .precision(Some(precision))
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };

        insta::assert_snapshot!(p(1 * 60 * 60, 0), @"1hr");
        insta::assert_snapshot!(pp(0, 1 * 60 * 60, 0), @"1hr");
        insta::assert_snapshot!(pp(1, 1 * 60 * 60, 0), @"1.0hr");
        insta::assert_snapshot!(pp(2, 1 * 60 * 60, 0), @"1.00hr");

        insta::assert_snapshot!(p(1 * 60 * 60 + 30 * 60, 0), @"1.5hrs");
        insta::assert_snapshot!(pp(0, 1 * 60 * 60 + 30 * 60, 0), @"1hr");
        insta::assert_snapshot!(pp(1, 1 * 60 * 60 + 30 * 60, 0), @"1.5hrs");
        insta::assert_snapshot!(pp(2, 1 * 60 * 60 + 30 * 60, 0), @"1.50hrs");

        insta::assert_snapshot!(p(1 * 60 * 60 + 3 * 60, 0), @"1.05hrs");
        insta::assert_snapshot!(p(1 * 60 * 60 + 3 * 60, 1), @"1.05hrs");
        insta::assert_snapshot!(p(1, 0), @"0.000277777hrs");
        // precision loss!
        insta::assert_snapshot!(p(1, 1), @"0.000277777hrs");
        insta::assert_snapshot!(p(0, 0), @"0hrs");
        // precision loss!
        insta::assert_snapshot!(p(0, 1), @"0hrs");

        insta::assert_snapshot!(
            printer().duration_to_string(&SignedDuration::MIN).unwrap(),
            @"2562047788015215.502499999hrs ago",
        );
    }

    #[test]
    fn print_duration_designator_fractional_minute() {
        let printer =
            || SpanPrinter::new().fractional(Some(FractionalUnit::Minute));
        let p = |secs, nanos| {
            printer()
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };
        let pp = |precision, secs, nanos| {
            printer()
                .precision(Some(precision))
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };

        insta::assert_snapshot!(p(1 * 60 * 60, 0), @"1hr");
        insta::assert_snapshot!(p(1 * 60 * 60 + 30 * 60, 0), @"1hr 30mins");

        insta::assert_snapshot!(p(60, 0), @"1min");
        insta::assert_snapshot!(pp(0, 60, 0), @"1min");
        insta::assert_snapshot!(pp(1, 60, 0), @"1.0min");
        insta::assert_snapshot!(pp(2, 60, 0), @"1.00min");

        insta::assert_snapshot!(p(90, 0), @"1.5mins");
        insta::assert_snapshot!(pp(0, 90, 0), @"1min");
        insta::assert_snapshot!(pp(1, 90, 0), @"1.5mins");
        insta::assert_snapshot!(pp(2, 90, 0), @"1.50mins");

        insta::assert_snapshot!(p(1 * 60 * 60, 1), @"1hr");
        insta::assert_snapshot!(p(63, 0), @"1.05mins");
        insta::assert_snapshot!(p(63, 1), @"1.05mins");
        insta::assert_snapshot!(p(1, 0), @"0.016666666mins");
        // precision loss!
        insta::assert_snapshot!(p(1, 1), @"0.016666666mins");
        insta::assert_snapshot!(p(0, 0), @"0mins");
        // precision loss!
        insta::assert_snapshot!(p(0, 1), @"0mins");

        insta::assert_snapshot!(
            printer().duration_to_string(&SignedDuration::MIN).unwrap(),
            @"2562047788015215hrs 30.149999999mins ago",
        );
    }

    #[test]
    fn print_duration_designator_fractional_second() {
        let printer =
            || SpanPrinter::new().fractional(Some(FractionalUnit::Second));
        let p = |secs, nanos| {
            printer()
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };
        let pp = |precision, secs, nanos| {
            printer()
                .precision(Some(precision))
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };

        insta::assert_snapshot!(p(1 * 60 * 60, 0), @"1hr");
        insta::assert_snapshot!(p(1 * 60 * 60 + 30 * 60, 0), @"1hr 30mins");

        insta::assert_snapshot!(p(1, 0), @"1sec");
        insta::assert_snapshot!(pp(0, 1, 0), @"1sec");
        insta::assert_snapshot!(pp(1, 1, 0), @"1.0sec");
        insta::assert_snapshot!(pp(2, 1, 0), @"1.00sec");

        insta::assert_snapshot!(p(1, 500_000_000), @"1.5secs");
        insta::assert_snapshot!(pp(0, 1, 500_000_000), @"1sec");
        insta::assert_snapshot!(pp(1, 1, 500_000_000), @"1.5secs");
        insta::assert_snapshot!(pp(2, 1, 500_000_000), @"1.50secs");

        insta::assert_snapshot!(p(1, 1), @"1.000000001secs");
        insta::assert_snapshot!(p(0, 1), @"0.000000001secs");
        insta::assert_snapshot!(p(0, 0), @"0secs");

        insta::assert_snapshot!(
            printer().duration_to_string(&SignedDuration::MIN).unwrap(),
            @"2562047788015215hrs 30mins 8.999999999secs ago",
        );
    }

    #[test]
    fn print_duration_designator_fractional_millisecond() {
        let printer = || {
            SpanPrinter::new().fractional(Some(FractionalUnit::Millisecond))
        };
        let p = |secs, nanos| {
            printer()
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };
        let pp = |precision, secs, nanos| {
            printer()
                .precision(Some(precision))
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };

        insta::assert_snapshot!(p(1 * 60 * 60, 0), @"1hr");
        insta::assert_snapshot!(p(1 * 60 * 60 + 30 * 60, 0), @"1hr 30mins");
        insta::assert_snapshot!(
            p(1 * 60 * 60 + 30 * 60 + 10, 0),
            @"1hr 30mins 10secs",
        );

        insta::assert_snapshot!(p(1, 0), @"1sec");
        insta::assert_snapshot!(pp(0, 1, 0), @"1sec");
        insta::assert_snapshot!(pp(1, 1, 0), @"1sec 0.0msecs");
        insta::assert_snapshot!(pp(2, 1, 0), @"1sec 0.00msecs");

        insta::assert_snapshot!(p(1, 500_000_000), @"1sec 500msecs");
        insta::assert_snapshot!(pp(0, 1, 1_500_000), @"1sec 1msec");
        insta::assert_snapshot!(pp(1, 1, 1_500_000), @"1sec 1.5msecs");
        insta::assert_snapshot!(pp(2, 1, 1_500_000), @"1sec 1.50msecs");

        insta::assert_snapshot!(p(0, 1_000_001), @"1.000001msecs");
        insta::assert_snapshot!(p(0, 0_000_001), @"0.000001msecs");
        insta::assert_snapshot!(p(0, 0), @"0msecs");

        insta::assert_snapshot!(
            printer().duration_to_string(&SignedDuration::MIN).unwrap(),
            @"2562047788015215hrs 30mins 8secs 999.999999msecs ago",
        );
    }

    #[test]
    fn print_duration_designator_fractional_microsecond() {
        let printer = || {
            SpanPrinter::new().fractional(Some(FractionalUnit::Microsecond))
        };
        let p = |secs, nanos| {
            printer()
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };
        let pp = |precision, secs, nanos| {
            printer()
                .precision(Some(precision))
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };

        insta::assert_snapshot!(p(1 * 60 * 60, 0), @"1hr");
        insta::assert_snapshot!(p(1 * 60 * 60 + 30 * 60, 0), @"1hr 30mins");
        insta::assert_snapshot!(
            p(1 * 60 * 60 + 30 * 60 + 10, 0),
            @"1hr 30mins 10secs",
        );

        insta::assert_snapshot!(p(1, 0), @"1sec");
        insta::assert_snapshot!(pp(0, 1, 0), @"1sec");
        insta::assert_snapshot!(pp(1, 1, 0), @"1sec 0.0µsecs");
        insta::assert_snapshot!(pp(2, 1, 0), @"1sec 0.00µsecs");

        insta::assert_snapshot!(p(1, 500_000_000), @"1sec 500msecs");
        insta::assert_snapshot!(pp(0, 1, 1_500_000), @"1sec 1msec 500µsecs");
        insta::assert_snapshot!(pp(1, 1, 1_500_000), @"1sec 1msec 500.0µsecs");
        insta::assert_snapshot!(pp(2, 1, 1_500_000), @"1sec 1msec 500.00µsecs");

        insta::assert_snapshot!(p(0, 1_000_001), @"1msec 0.001µsecs");
        insta::assert_snapshot!(p(0, 0_000_001), @"0.001µsecs");
        insta::assert_snapshot!(p(0, 0), @"0µsecs");

        insta::assert_snapshot!(
            printer().duration_to_string(&SignedDuration::MIN).unwrap(),
            @"2562047788015215hrs 30mins 8secs 999msecs 999.999µsecs ago",
        );
    }

    #[test]
    fn print_span_hms() {
        let printer = || SpanPrinter::new().hours_minutes_seconds(true);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.second()), @"00:00:01");
        insta::assert_snapshot!(p(2.seconds()), @"00:00:02");
        insta::assert_snapshot!(p(10.seconds()), @"00:00:10");
        insta::assert_snapshot!(p(100.seconds()), @"00:00:100");

        insta::assert_snapshot!(p(1.minute()), @"00:01:00");
        insta::assert_snapshot!(p(2.minutes()), @"00:02:00");
        insta::assert_snapshot!(p(10.minutes()), @"00:10:00");
        insta::assert_snapshot!(p(100.minutes()), @"00:100:00");

        insta::assert_snapshot!(p(1.hour()), @"01:00:00");
        insta::assert_snapshot!(p(2.hours()), @"02:00:00");
        insta::assert_snapshot!(p(10.hours()), @"10:00:00");
        insta::assert_snapshot!(p(100.hours()), @"100:00:00");

        insta::assert_snapshot!(
            p(1.hour().minutes(1).seconds(1)),
            @"01:01:01",
        );
        insta::assert_snapshot!(
            p(2.hours().minutes(2).seconds(2)),
            @"02:02:02",
        );
        insta::assert_snapshot!(
            p(10.hours().minutes(10).seconds(10)),
            @"10:10:10",
        );
        insta::assert_snapshot!(
            p(100.hours().minutes(100).seconds(100)),
            @"100:100:100",
        );
    }

    #[test]
    fn print_span_hms_fraction_auto() {
        let printer = || SpanPrinter::new().hours_minutes_seconds(true);
        let p = |span| printer().span_to_string(&span).unwrap();

        insta::assert_snapshot!(p(1.nanosecond()), @"00:00:00.000000001");
        insta::assert_snapshot!(p(-1.nanosecond()), @"-00:00:00.000000001");
        insta::assert_snapshot!(
            printer().direction(Direction::ForceSign).span_to_string(&1.nanosecond()).unwrap(),
            @"+00:00:00.000000001",
        );

        insta::assert_snapshot!(
            p(1.second().nanoseconds(123)),
            @"00:00:01.000000123",
        );
        insta::assert_snapshot!(
            p(1.second().milliseconds(123)),
            @"00:00:01.123",
        );
        insta::assert_snapshot!(
            p(1.second().milliseconds(1_123)),
            @"00:00:02.123",
        );
        insta::assert_snapshot!(
            p(1.second().milliseconds(61_123)),
            @"00:00:62.123",
        );
    }

    #[test]
    fn print_span_hms_fraction_fixed_precision() {
        let printer = || SpanPrinter::new().hours_minutes_seconds(true);
        let p = |precision, span| {
            printer().precision(Some(precision)).span_to_string(&span).unwrap()
        };

        insta::assert_snapshot!(p(3, 1.second()), @"00:00:01.000");
        insta::assert_snapshot!(
            p(3, 1.second().milliseconds(1)),
            @"00:00:01.001",
        );
        insta::assert_snapshot!(
            p(3, 1.second().milliseconds(123)),
            @"00:00:01.123",
        );
        insta::assert_snapshot!(
            p(3, 1.second().milliseconds(100)),
            @"00:00:01.100",
        );

        insta::assert_snapshot!(p(0, 1.second()), @"00:00:01");
        insta::assert_snapshot!(p(0, 1.second().milliseconds(1)), @"00:00:01");
        insta::assert_snapshot!(
            p(1, 1.second().milliseconds(999)),
            @"00:00:01.9",
        );
    }

    #[test]
    fn print_duration_hms() {
        let printer = || SpanPrinter::new().hours_minutes_seconds(true);
        let p = |secs| {
            printer()
                .duration_to_string(&SignedDuration::from_secs(secs))
                .unwrap()
        };

        // Note the differences with `Span`, since with a `SignedDuration`,
        // all units are balanced.

        insta::assert_snapshot!(p(1), @"00:00:01");
        insta::assert_snapshot!(p(2), @"00:00:02");
        insta::assert_snapshot!(p(10), @"00:00:10");
        insta::assert_snapshot!(p(100), @"00:01:40");

        insta::assert_snapshot!(p(1 * 60), @"00:01:00");
        insta::assert_snapshot!(p(2 * 60), @"00:02:00");
        insta::assert_snapshot!(p(10 * 60), @"00:10:00");
        insta::assert_snapshot!(p(100 * 60), @"01:40:00");

        insta::assert_snapshot!(p(1 * 60 * 60), @"01:00:00");
        insta::assert_snapshot!(p(2 * 60 * 60), @"02:00:00");
        insta::assert_snapshot!(p(10 * 60 * 60), @"10:00:00");
        insta::assert_snapshot!(p(100 * 60 * 60), @"100:00:00");

        insta::assert_snapshot!(
            p(60 * 60 + 60 + 1),
            @"01:01:01",
        );
        insta::assert_snapshot!(
            p(2 * 60 * 60 + 2 * 60 + 2),
            @"02:02:02",
        );
        insta::assert_snapshot!(
            p(10 * 60 * 60 + 10 * 60 + 10),
            @"10:10:10",
        );
        insta::assert_snapshot!(
            p(100 * 60 * 60 + 100 * 60 + 100),
            @"101:41:40",
        );
    }

    #[test]
    fn print_duration_hms_fraction_auto() {
        let printer = || SpanPrinter::new().hours_minutes_seconds(true);
        let p = |secs, nanos| {
            printer()
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };

        insta::assert_snapshot!(p(0, 1), @"00:00:00.000000001");
        insta::assert_snapshot!(p(0, -1), @"-00:00:00.000000001");
        insta::assert_snapshot!(
            printer().direction(Direction::ForceSign).duration_to_string(
                &SignedDuration::new(0, 1),
            ).unwrap(),
            @"+00:00:00.000000001",
        );

        insta::assert_snapshot!(
            p(1, 123),
            @"00:00:01.000000123",
        );
        insta::assert_snapshot!(
            p(1, 123_000_000),
            @"00:00:01.123",
        );
        insta::assert_snapshot!(
            p(1, 1_123_000_000),
            @"00:00:02.123",
        );
        insta::assert_snapshot!(
            p(61, 1_123_000_000),
            @"00:01:02.123",
        );
    }

    #[test]
    fn print_duration_hms_fraction_fixed_precision() {
        let printer = || SpanPrinter::new().hours_minutes_seconds(true);
        let p = |precision, secs, nanos| {
            printer()
                .precision(Some(precision))
                .duration_to_string(&SignedDuration::new(secs, nanos))
                .unwrap()
        };

        insta::assert_snapshot!(p(3, 1, 0), @"00:00:01.000");
        insta::assert_snapshot!(
            p(3, 1, 1_000_000),
            @"00:00:01.001",
        );
        insta::assert_snapshot!(
            p(3, 1, 123_000_000),
            @"00:00:01.123",
        );
        insta::assert_snapshot!(
            p(3, 1, 100_000_000),
            @"00:00:01.100",
        );

        insta::assert_snapshot!(p(0, 1, 0), @"00:00:01");
        insta::assert_snapshot!(p(0, 1, 1_000_000), @"00:00:01");
        insta::assert_snapshot!(
            p(1, 1, 999_000_000),
            @"00:00:01.9",
        );
    }
}
