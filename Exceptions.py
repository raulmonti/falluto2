################################################################################
class BaseException():
    def __init__(self):
        self.error = ""
    def __str__(self):
        return str(self.error)
    def __repr__(self):
        return repr(self.error)
    def __unicode__(self):
        return unicode(self.error)


################################################################################
class LethalException(BaseException):
    def __init__(self, error):
        BaseException.__init__(self)
        assert isinstance(error, unicode)
        self.error = error
