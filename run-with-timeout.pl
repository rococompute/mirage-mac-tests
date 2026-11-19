#!/usr/bin/perl
# Run a command in its own process group, bounding its lifetime and cleaning
# up descendants on success, timeout, or a signal to this supervisor.
# Uses only modules shipped with macOS Perl. Exit 124 means timeout.
use strict;
use warnings;
use POSIX qw(setpgid WNOHANG);
use Time::HiRes qw(time sleep);
use Errno qw(EINTR);

my $seconds = shift @ARGV;
die "usage: $0 SECONDS COMMAND [ARG...]\n"
    unless defined($seconds) && $seconds =~ /^\d+(?:\.\d+)?$/ && $seconds > 0 && @ARGV;
my $signal = 0;
$SIG{INT} = sub { $signal = 2 };
$SIG{TERM} = sub { $signal = 15 };
$SIG{HUP} = sub { $signal = 1 };
my $pid = fork();
die "fork: $!\n" unless defined $pid;
if (!$pid) {
    $SIG{INT} = $SIG{TERM} = $SIG{HUP} = 'DEFAULT';
    setpgid(0, 0) == 0 or die "setpgid: $!\n";
    exec @ARGV;
    die "exec $ARGV[0]: $!\n";
}
# Close the race before the child executes. The child also sets its group.
setpgid($pid, $pid);
my $deadline = time() + $seconds;
my ($stopping, $timed_out, $status) = (0, 0, undef);
while (1) {
    my $done = waitpid($pid, WNOHANG);
    if ($done == $pid) { $status = $?; last }
    next if $done < 0 && $! == EINTR;
    die "waitpid: $!\n" if $done < 0;
    if (!$stopping && ($signal || time() >= $deadline)) {
        $timed_out = !$signal;
        kill 'TERM', -$pid;
        $stopping = 1;
        $deadline = time() + 2;
    }
    if ($stopping && time() >= $deadline) {
        kill 'KILL', -$pid;
    }
    sleep 0.02;
}
# The leader may have exited while a descendant is still alive.
kill 'TERM', -$pid;
my $grace = time() + 0.2;
while (kill(0, -$pid) && time() < $grace) { sleep 0.02 }
kill 'KILL', -$pid;
exit 124 if $timed_out;
exit(128 + $signal) if $signal;
exit(($status & 127) ? 128 + ($status & 127) : $status >> 8);
