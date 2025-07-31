import argparse

class DictAction(argparse.Action):
    def __call__(self, parser, namespace, values, option_string=None):
        assert isinstance(getattr(namespace, self.dest), dict), f"Use ArgumentParser.set_defaults() to initialize {self.dest} to dict()"
        name = option_string.lstrip(parser.prefix_chars).replace("-", "_")
        getattr(namespace, self.dest)[name] = values

def parser_func(release_version='unknown SBY version'):
    parser = argparse.ArgumentParser(prog="sby",
            usage="%(prog)s [options] [<jobname>.sby [tasknames] | <dirname>]")
    parser.set_defaults(exe_paths=dict())

    parser.add_argument("-d", metavar="<dirname>", dest="workdir",
            help="set workdir name. default: <jobname> or <jobname>_<taskname>. When there is more than one task, use --prefix instead")
    parser.add_argument("--prefix", metavar="<dirname>", dest="workdir_prefix",
            help="set the workdir name prefix. `_<taskname>` will be appended to the path for each task")
    parser.add_argument("-f", action="store_true", dest="force",
            help="remove workdir if it already exists")
    parser.add_argument("-b", action="store_true", dest="backup",
            help="backup workdir if it already exists")
    parser.add_argument("-t", action="store_true", dest="tmpdir",
            help="run in a temporary workdir (remove when finished)")
    parser.add_argument("-T", metavar="<taskname>", action="append", dest="tasknames", default=list(),
            help="add taskname (useful when sby file is read from stdin)")
    parser.add_argument("-E", action="store_true", dest="throw_err",
            help="throw an exception (incl stack trace) for most errors")
    parser.add_argument("-j", metavar="<N>", type=int, dest="jobcount",
            help="maximum number of processes to run in parallel")
    parser.add_argument("--sequential", action="store_true", dest="sequential",
            help="run tasks in sequence, not in parallel")
    parser.add_argument("--live", action="append", choices=["csv", "jsonl"], dest="live_formats",
            help="print live updates of property statuses during task execution, may be specified multiple times")

    parser.add_argument("--autotune", action="store_true", dest="autotune",
            help="automatically find a well performing engine and engine configuration for each task")
    parser.add_argument("--autotune-config", dest="autotune_config",
            help="read an autotune configuration file (overrides the sby file's autotune options)")

    parser.add_argument("--yosys", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--abc", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--smtbmc", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--witness", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--suprove", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--aigbmc", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--avy", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--rIC3", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--btormc", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths")
    parser.add_argument("--pono", metavar="<path_to_executable>",
            action=DictAction, dest="exe_paths",
            help="configure which executable to use for the respective tool")
    parser.add_argument("--dumpcfg", action="store_true", dest="dump_cfg",
            help="print the pre-processed configuration file")
    parser.add_argument("--dumptags", action="store_true", dest="dump_tags",
            help="print the list of task tags")
    parser.add_argument("--dumptasks", action="store_true", dest="dump_tasks",
            help="print the list of tasks")
    parser.add_argument("--dumpdefaults", action="store_true", dest="dump_defaults",
            help="print the list of default tasks")
    parser.add_argument("--dumptaskinfo", action="store_true", dest="dump_taskinfo",
            help="output a summary of tasks as JSON")
    parser.add_argument("--dumpfiles", action="store_true", dest="dump_files",
            help="print the list of source files")
    parser.add_argument("--setup", action="store_true", dest="setupmode",
            help="set up the working directory and exit")
    parser.add_argument("--link", action="store_true", dest="linkmode",
            help="make symbolic links to source files instead of copying them")

    parser.add_argument("--status", action="store_true", dest="status",
            help="summarize the contents of the status database")
    parser.add_argument("--statusfmt", action="store", default="", choices=["csv", "jsonl"], dest="status_format",
            help="print the most recent status for each property in specified format")
    parser.add_argument("--latest", action="store_true", dest="status_latest",
            help="only check statuses from the most recent run of a task")
    parser.add_argument("--statusreset", action="store_true", dest="status_reset",
            help="reset the contents of the status database")
    parser.add_argument("--statuscancels", action="store_true", dest="status_cancels",
            help="intertask cancellations can be triggered by the status database")

    parser.add_argument("--taskstatus", action="store_true", dest="task_status",
            help="display the status of tasks in the status database")

    parser.add_argument("--init-config-file", dest="init_config_file",
            help="create a default .sby config file")
    parser.add_argument("sbyfile", metavar="<jobname>.sby | <dirname>", nargs="?",
            help=".sby file OR directory containing config.sby file")
    parser.add_argument("arg_tasknames", metavar="tasknames", nargs="*",
            help="tasks to run (only valid when <jobname>.sby is used)")

    parser.add_argument('--version', action='version', version=release_version)

    return parser
